mod item_context;
pub mod typecheck;

use derive_more::{Display, From};
use derive_new::new;
use itertools::Itertools;
use mist_syntax::{
    ast::{
        self,
        operators::{BinaryOp, UnaryOp},
        AttrFlags, HasAttrs, HasName, Spanned,
    },
    ptr::AstPtr,
    AstNode, Parse, SourceSpan,
};
use tracing::error;

use crate::{
    hir::{self, typecheck::Typed},
    util::{impl_idx, IdxWrap},
    TypeCheckErrors,
};

pub use item_context::{ItemContext, ItemSourceMap, SpanOrAstPtr};
use typecheck::{TypeCheckError, TypeCheckErrorKind, TypeChecker};

pub mod pretty;

mod ident {
    use super::*;

    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Ident {
        inner: String,
        span: SourceSpan,
    }
    impl Ident {
        pub fn as_str(&self) -> &str {
            self
        }
    }
    impl From<ast::Name> for Ident {
        fn from(value: ast::Name) -> Self {
            Ident {
                inner: value.to_string(),
                span: value.span(),
            }
        }
    }
    impl From<ast::NameRef> for Ident {
        fn from(value: ast::NameRef) -> Self {
            Ident {
                inner: value.to_string(),
                span: value.span(),
            }
        }
    }
    impl std::fmt::Display for Ident {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.inner.fmt(f)
        }
    }
    impl std::fmt::Debug for Ident {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.inner.fmt(f)
        }
    }
    impl std::ops::Deref for Ident {
        type Target = str;

        fn deref(&self) -> &Self::Target {
            &self.inner
        }
    }
    impl Spanned for &'_ Ident {
        fn span(self) -> SourceSpan {
            self.span
        }
    }
}

pub use ident::*;

#[salsa::input]
pub struct SourceProgram {
    #[return_ref]
    pub text: String,
}

#[salsa::tracked]
pub struct Program {
    #[return_ref]
    pub parse: Parse<ast::SourceFile>,
    #[return_ref]
    pub items: Vec<ItemId>,
}

#[salsa::tracked]
pub fn parse_program(db: &dyn crate::Db, source: SourceProgram) -> Program {
    let parse = mist_syntax::parse(source.text(db));
    let items = parse
        .tree()
        .items()
        .map(|item| match item {
            ast::Item::Const(node) => ItemId::new(db, AstPtr::new(&node).into()),
            ast::Item::Fn(node) => ItemId::new(db, AstPtr::new(&node).into()),
            ast::Item::Struct(node) => ItemId::new(db, AstPtr::new(&node).into()),
            ast::Item::TypeInvariant(node) => ItemId::new(db, AstPtr::new(&node).into()),
            ast::Item::Macro(node) => ItemId::new(db, AstPtr::new(&node).into()),
        })
        .collect();
    Program::new(db, parse, items)
}

#[salsa::tracked]
pub fn intern_item(db: &dyn crate::Db, program: Program, item_id: ItemId) -> Option<Item> {
    let root = program.parse(db).tree();
    item(db, &root, item_id)
}

pub fn item(db: &dyn crate::Db, root: &ast::SourceFile, item_id: ItemId) -> Option<Item> {
    Some(match item_id.data(db) {
        ItemData::Const { .. } => return None,
        ItemData::Fn { ast } => {
            let f = ast.to_node(root.syntax());
            let name = f.name().unwrap();
            let attrs = f.attr_flags();

            if !f.is_ghost() && f.body().is_none() {
                let err = TypeCheckError {
                    input: root.to_string(),
                    span: f
                        .semicolon_token()
                        .map(|t| t.span())
                        .unwrap_or_else(|| name.span()),
                    label: None,
                    help: None,
                    kind: TypeCheckErrorKind::NonGhostFunctionWithoutBody,
                };
                TypeCheckErrors::push(db, err);
            }

            Function::new(db, ast, name.into(), attrs).into()
        }
        ItemData::Struct { ast } => {
            let s = ast.to_node(root.syntax());
            let name = Ident::from(s.name().unwrap());
            let fields = s
                .struct_fields()
                .map(|f| {
                    let is_ghost = f.is_ghost();
                    let name = f.name().unwrap();
                    StructFieldInner {
                        name: name.into(),
                        is_ghost,
                        ty: f.ty().as_ref().map(AstPtr::new),
                    }
                })
                .collect();
            let data = TypeDeclData::Struct(Struct::new(db, ast, name.clone(), fields));
            TypeDecl::new(db, name, data).into()
        }
        ItemData::TypeInvariant { ast } => {
            let i = ast.to_node(root.syntax());
            let name = Ident::from(i.name_ref().unwrap());
            TypeInvariant::new(db, ast, name).into()
        }
        ItemData::Macro { .. } => return None,
    })
}

#[salsa::tracked]
pub fn item_lower(
    db: &dyn crate::Db,
    program: Program,
    item_id: ItemId,
    item: Item,
) -> Option<(ItemContext, ItemSourceMap)> {
    let span = tracing::span!(
        tracing::Level::DEBUG,
        "hir::item_lower",
        "{}",
        item.name(db)
    );
    let _enter = span.enter();

    let root = program.parse(db).tree();

    match item {
        Item::Type(ty_decl) => match &ty_decl.data(db) {
            TypeDeclData::Struct(_) => {
                let mut checker = TypeChecker::init(db, program, &root, item_id);

                if let Some(self_ty) = checker.cx.self_ty() {
                    let related_invs = program
                        .items(db)
                        .iter()
                        .filter_map(|&item_id| {
                            if let Some(hir::Item::TypeInvariant(inv)) =
                                hir::item(db, &root, item_id)
                            {
                                if checker.find_named_type(inv.name(db)) == self_ty {
                                    return Some(inv);
                                }
                            }
                            None
                        })
                        .collect_vec();

                    for ty_inv in related_invs {
                        if let Some(ast_body) = ty_inv.body(db, &root) {
                            let body = checker.check_block(&ast_body, |f| f);
                            let ret = checker.bool().ghost();
                            checker.expect_ty(ty_inv.name(db).span(), ret, body.return_ty);
                            let body_expr = checker.alloc_expr(
                                Expr::new(body.return_ty, ExprData::Block(body)),
                                &ast::Expr::from(ast_body),
                            );
                            checker.cx.self_invariants.push(body_expr);
                        }
                    }
                }

                Some(checker.into())
            }
        },
        Item::TypeInvariant(ty_inv) => {
            let mut checker = TypeChecker::init(db, program, &root, item_id);
            if let Some(ast_body) = ty_inv.body(db, &root) {
                let body = checker.check_block(&ast_body, |f| f);
                let ret = checker.bool().ghost();
                checker.expect_ty(ty_inv.name(db).span(), ret, body.return_ty);
                let ret_ty = checker.unsourced_ty(ret);
                checker.set_return_ty(ret_ty);
                checker.set_body_expr_from_block(body, ast_body);
            }
            Some(checker.into())
        }
        Item::Function(function) => {
            let mut checker = TypeChecker::init(db, program, &root, item_id);
            let ast_body = function.body(db, &root);
            let body = ast_body
                .as_ref()
                .map(|ast_body| checker.check_block(ast_body, |f| f));
            let is_ghost = function.attrs(db).is_ghost();
            if let Some(body) = body {
                if let Some(ret) = function.ret(db, &root) {
                    let ret = checker
                        .find_type_src(&ret)
                        .with_ghost(is_ghost)
                        .ts(&mut checker);
                    checker.expect_ty(
                        function
                            .ret(db, &root)
                            .map(|ret| ret.span())
                            .unwrap_or_else(|| function.name(db).span()),
                        checker.cx[ret].ty,
                        body.return_ty,
                    );
                } else {
                    checker.expect_ty(
                        function.name(db).span(),
                        checker.void().with_ghost(is_ghost),
                        body.return_ty,
                    );
                }
                checker.set_body_expr_from_block(body, ast_body.unwrap());
            }
            if let Some(ret) = function.ret(db, &root) {
                let ret_ty = checker.find_type_src(&ret);
                checker.set_return_ty(ret_ty);
            }
            Some(checker.into())
        }
    }
}

#[salsa::interned]
pub struct ItemId {
    pub data: ItemData,
}

impl ItemId {
    pub fn syntax(&self, db: &dyn crate::Db, root: &ast::SourceFile) -> mist_syntax::SyntaxNode {
        self.data(db).syntax(root)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, From)]
pub enum ItemData {
    Const { ast: AstPtr<ast::Const> },
    Fn { ast: AstPtr<ast::Fn> },
    Struct { ast: AstPtr<ast::Struct> },
    TypeInvariant { ast: AstPtr<ast::TypeInvariant> },
    Macro { ast: AstPtr<ast::Macro> },
}
impl ItemData {
    fn syntax(&self, root: &ast::SourceFile) -> mist_syntax::SyntaxNode {
        match self {
            ItemData::Const { ast } => ast.to_node(root.syntax()).syntax().clone(),
            ItemData::Fn { ast } => ast.to_node(root.syntax()).syntax().clone(),
            ItemData::Struct { ast } => ast.to_node(root.syntax()).syntax().clone(),
            ItemData::TypeInvariant { ast } => ast.to_node(root.syntax()).syntax().clone(),
            ItemData::Macro { ast } => ast.to_node(root.syntax()).syntax().clone(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub enum Item {
    Type(TypeDecl),
    TypeInvariant(TypeInvariant),
    Function(Function),
}

impl Item {
    pub fn name(&self, db: &dyn crate::Db) -> Ident {
        match self {
            Item::Type(t) => t.name(db).clone(),
            Item::TypeInvariant(t) => t.name(db),
            Item::Function(f) => f.name(db).clone(),
        }
    }
}

#[salsa::tracked]
pub struct TypeDecl {
    #[return_ref]
    pub name: Ident,
    pub data: TypeDeclData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeDeclData {
    Struct(Struct),
}

#[salsa::interned]
pub struct Function {
    #[return_ref]
    syntax: AstPtr<ast::Fn>,
    #[return_ref]
    pub name: Ident,
    pub attrs: AttrFlags,
}

impl Function {
    pub fn body(&self, db: &dyn crate::Db, root: &ast::SourceFile) -> Option<ast::BlockExpr> {
        self.syntax(db).to_node(root.syntax()).body()
    }
    pub fn param_list(
        &self,
        db: &dyn crate::Db,
        root: &ast::SourceFile,
    ) -> impl Iterator<Item = Param<Ident, Option<ast::Type>>> + '_ {
        self.syntax(db)
            .to_node(root.syntax())
            .param_list()
            .into_iter()
            .flat_map(|param_list| {
                param_list
                    .params()
                    .map(|param| -> Param<Ident, Option<ast::Type>> {
                        Param {
                            is_ghost: param.is_ghost(),
                            name: param
                                .name()
                                .map(Ident::from)
                                .expect("param did not have a name"),
                            ty: param.ty(),
                        }
                    })
            })
    }
    pub fn ret(&self, db: &dyn crate::Db, root: &ast::SourceFile) -> Option<ast::Type> {
        self.syntax(db).to_node(root.syntax()).ret()
    }
    pub fn conditions(
        &self,
        db: &dyn crate::Db,
        root: &ast::SourceFile,
    ) -> impl Iterator<Item = ast::Condition> {
        self.syntax(db).to_node(root.syntax()).conditions()
    }
    pub fn decreases(&self, db: &dyn crate::Db, root: &ast::SourceFile) -> Option<ast::Decreases> {
        self.syntax(db).to_node(root.syntax()).decreases()
    }
}

#[salsa::interned]
pub struct VariableId {
    #[return_ref]
    pub text: String,
}

#[salsa::tracked]
pub struct Variable {
    #[id]
    pub name: VariableId,
}
impl_idx!(VariableIdx, Variable, default_debug);
#[derive(new, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VariableRef {
    idx: VariableIdx,
    span: SourceSpan,
}

impl VariableRef {
    pub fn idx(&self) -> VariableIdx {
        self.idx
    }
}
impl Spanned for VariableRef {
    fn span(self) -> SourceSpan {
        self.span
    }
}
impl Spanned for &'_ VariableRef {
    fn span(self) -> SourceSpan {
        self.span
    }
}
impl From<VariableRef> for VariableIdx {
    fn from(value: VariableRef) -> Self {
        value.idx
    }
}
impl From<&'_ VariableRef> for VariableIdx {
    fn from(value: &VariableRef) -> Self {
        value.idx
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Param<I, T = TypeSrcId> {
    pub is_ghost: bool,
    pub name: I,
    pub ty: T,
}

impl<I, T> Param<I, T> {
    pub fn map_var<J>(&self, f: impl FnOnce(&I) -> J) -> Param<J, T>
    where
        T: Clone,
    {
        Param {
            is_ghost: self.is_ghost,
            name: f(&self.name),
            ty: self.ty.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Condition {
    Requires(Vec<ExprIdx>),
    Ensures(Vec<ExprIdx>),
}

impl Condition {
    pub fn exprs(&self) -> &[ExprIdx] {
        match self {
            Self::Requires(it) | Self::Ensures(it) => it,
        }
    }
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Decreases {
    #[default]
    Unspecified,
    Expr(ExprIdx),
    Inferred,
}

impl_idx!(ExprIdx, Expr, default_debug);
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expr {
    pub ty: TypeId,
    pub data: ExprData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprData {
    Literal(Literal),
    Self_,
    Ident(VariableRef),
    Block(Block),
    Field {
        expr: ExprIdx,
        field_name: Ident,
        field: Option<Field>,
    },
    Struct {
        struct_declaration: Struct,
        struct_span: SourceSpan,
        fields: Vec<StructExprField>,
    },
    Missing,
    If(IfExpr),
    Call {
        expr: ExprIdx,
        args: Vec<ExprIdx>,
    },
    Unary {
        op: UnaryOp,
        inner: ExprIdx,
    },
    Bin {
        lhs: ExprIdx,
        op: BinaryOp,
        rhs: ExprIdx,
    },
    Ref {
        is_mut: bool,
        expr: ExprIdx,
    },
    Index {
        base: ExprIdx,
        index: ExprIdx,
    },
    List {
        elems: Vec<ExprIdx>,
    },
    Quantifier {
        quantifier: Quantifier,
        params: Vec<Param<VariableIdx>>,
        expr: ExprIdx,
    },
    Result,
    Range {
        lhs: Option<ExprIdx>,
        rhs: Option<ExprIdx>,
    },
    Return(Option<ExprIdx>),
    NotNull(ExprIdx),
}
#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    #[display(fmt = "null")]
    Null,
    #[display(fmt = "{_0}")]
    Int(i64),
    #[display(fmt = "{_0}")]
    Bool(bool),
}

impl Literal {
    pub fn as_bool(&self) -> Option<&bool> {
        if let Self::Bool(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_int(&self) -> Option<&i64> {
        if let Self::Int(v) = self {
            Some(v)
        } else {
            None
        }
    }
}
#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Quantifier {
    #[display(fmt = "forall")]
    Forall,
    #[display(fmt = "exists")]
    Exists,
}
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructExprField {
    pub decl: Field,
    pub name: Ident,
    pub value: ExprIdx,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IfExpr {
    pub if_span: SourceSpan,
    pub is_ghost: bool,
    pub return_ty: TypeId,
    pub condition: ExprIdx,
    pub then_branch: ExprIdx,
    pub else_branch: Option<ExprIdx>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    pub stmts: Vec<Statement>,
    pub tail_expr: Option<ExprIdx>,
    pub return_ty: TypeId,
}

#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Statement {
    pub span: SourceSpan,
    pub data: StatementData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StatementData {
    Expr(ExprIdx),
    Let {
        variable: VariableRef,
        explicit_ty: Option<TypeSrcId>,
        initializer: ExprIdx,
    },
    While {
        expr: ExprIdx,
        invariants: Vec<Vec<ExprIdx>>,
        decreases: Decreases,
        body: Block,
    },
    Assertion {
        kind: AssertionKind,
        exprs: Vec<ExprIdx>,
    },
}

#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AssertionKind {
    #[display(fmt = "assert")]
    Assert,
    #[display(fmt = "assume")]
    Assume,
    #[display(fmt = "inhale")]
    Inhale,
    #[display(fmt = "exhale")]
    Exhale,
}

impl_idx!(TypeSrcId, TypeSrc, default_debug);
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeSrc {
    pub data: Option<TypeData<TypeSrcId>>,
    pub ty: TypeId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(TypeDataIdx);
impl_idx!(TypeDataIdx, TypeData, default_debug);

impl ena::unify::UnifyKey for TypeId {
    type Value = TypeData;

    fn index(&self) -> u32 {
        self.0.into_raw().into()
    }

    fn from_index(u: u32) -> Self {
        Self(TypeDataIdx::from_raw(u.into()))
    }

    fn tag() -> &'static str {
        "TypeId"
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeData<T = TypeId> {
    Error,
    Void,
    Ghost(T),
    Ref {
        is_mut: bool,
        inner: T,
    },
    List(T),
    Optional(T),
    Primitive(Primitive),
    Struct(Struct),
    Null,
    Function {
        attrs: AttrFlags,
        name: Option<Ident>,
        params: Vec<Param<Ident>>,
        return_ty: T,
    },
    Range(T),
    Free,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Primitive {
    Int,
    Bool,
}

impl ena::unify::UnifyValue for TypeData {
    type Error = ();

    fn unify_values(ty1: &Self, ty2: &Self) -> Result<Self, ()> {
        match (ty1, ty2) {
            (TypeData::Free, other) | (other, TypeData::Free) => Ok(other.clone()),
            _ => {
                error!("could not unify {ty1:?} with {ty2:?}");
                Err(())
            }
        }
    }
}

impl<T> TypeData<T> {
    pub fn map<S>(&self, mut f: impl FnMut(&T) -> S) -> TypeData<S> {
        match self {
            TypeData::Error => TypeData::Error,
            TypeData::Void => TypeData::Void,
            TypeData::Ghost(it) => TypeData::Ghost(f(it)),
            TypeData::Ref { is_mut, inner } => TypeData::Ref {
                is_mut: *is_mut,
                inner: f(inner),
            },
            TypeData::List(it) => TypeData::List(f(it)),
            TypeData::Optional(it) => TypeData::Optional(f(it)),
            TypeData::Primitive(it) => TypeData::Primitive(it.clone()),
            TypeData::Struct(it) => TypeData::Struct(*it),
            TypeData::Null => TypeData::Null,
            TypeData::Function {
                attrs,
                name,
                params,
                return_ty,
            } => TypeData::Function {
                attrs: *attrs,
                name: name.clone(),
                params: params.clone(),
                return_ty: f(return_ty),
            },
            TypeData::Range(it) => TypeData::Range(f(it)),
            TypeData::Free => TypeData::Free,
        }
    }

    pub fn is_void(&self) -> bool {
        matches!(self, TypeData::Void)
    }
}
impl TypeData<TypeSrcId> {
    pub fn canonical(&self, cx: &ItemContext) -> TypeData {
        self.map(|&id| cx[id].ty)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructFieldInner {
    name: Ident,
    is_ghost: bool,
    ty: Option<AstPtr<ast::Type>>,
}

#[salsa::interned]
pub struct Struct {
    #[return_ref]
    node: AstPtr<ast::Struct>,
    pub name: Ident,
    #[return_ref]
    fields_inner: Vec<StructFieldInner>,
}

impl Struct {
    pub fn ast_fields(
        &self,
        db: &dyn crate::Db,
        root: &ast::SourceFile,
    ) -> impl Iterator<Item = ast::StructField> + '_ {
        self.node(db).to_node(root.syntax()).struct_fields()
    }
    pub fn fields<'db>(&self, db: &'db dyn crate::Db) -> impl Iterator<Item = Field> + 'db {
        let s = *self;
        self.fields_inner(db).iter().map(move |f| Field {
            parent: FieldParent::Struct(s),
            name: f.name.clone(),
            is_ghost: f.is_ghost,
            ty: f.ty.clone(),
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FieldParent {
    Struct(Struct),
    List(TypeId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Field {
    pub parent: FieldParent,
    pub name: Ident,
    pub is_ghost: bool,
    ty: Option<AstPtr<ast::Type>>,
}

impl Field {
    pub fn ty(&self, _db: &dyn crate::Db, root: &ast::SourceFile) -> Option<ast::Type> {
        self.ty.as_ref().map(|ty| ty.to_node(root.syntax()))
    }
}

#[salsa::interned]
pub struct TypeInvariant {
    #[return_ref]
    node: AstPtr<ast::TypeInvariant>,
    pub name: Ident,
}

impl TypeInvariant {
    pub fn body(&self, db: &dyn crate::Db, root: &ast::SourceFile) -> Option<ast::BlockExpr> {
        self.node(db).to_node(root.syntax()).block_expr()
    }
}
