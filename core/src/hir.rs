mod item_context;
mod lower;
pub mod typecheck;

use derive_more::Display;
use derive_new::new;
use mist_syntax::{
    ast::{
        self,
        operators::{BinaryOp, UnaryOp},
        AttrFlags, HasAttrs, HasName, Spanned,
    },
    SourceSpan,
};
use tracing::error;

use crate::{hir::typecheck::Typed, TypeCheckErrors};

pub use item_context::{ItemContext, ItemSourceMap};
use typecheck::{TypeCheckError, TypeCheckErrorKind, TypeChecker};

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
    pub program: mist_syntax::ast::SourceFile,
    #[return_ref]
    pub items: Vec<ItemId>,
    #[return_ref]
    pub errors: Vec<mist_syntax::ParseError>,
}

#[salsa::tracked]
pub fn parse_program(db: &dyn crate::Db, source: SourceProgram) -> Program {
    let (program, errors) = mist_syntax::parse(source.text(db));
    let items = program
        .items()
        .map(|item| match item {
            ast::Item::Const(node) => ItemId::new(db, ItemData::Const { ast: node }),
            ast::Item::Fn(node) => ItemId::new(db, ItemData::Fn { ast: node }),
            ast::Item::Struct(node) => ItemId::new(db, ItemData::Struct { ast: node }),
            ast::Item::TypeInvariant(node) => {
                ItemId::new(db, ItemData::TypeInvariant { ast: node })
            }
            ast::Item::Macro(node) => ItemId::new(db, ItemData::Macro { ast: node }),
        })
        .collect();
    Program::new(db, program, items, errors)
}

#[salsa::tracked]
pub fn item(db: &dyn crate::Db, program: Program, item_id: ItemId) -> Option<Item> {
    match item_id.data(db) {
        ItemData::Const { .. } => None,
        ItemData::Fn { ast: f } => {
            let name = if let Some(name) = f.name() {
                name
            } else {
                todo!()
            };
            let attrs = f.attr_flags();
            let param_list = f
                .param_list()
                .map(|param_list| {
                    param_list
                        .params()
                        .map(|param| -> Param<Ident, Option<mist_syntax::ast::Type>> {
                            Param {
                                is_ghost: param.is_ghost(),
                                name: param
                                    .name()
                                    .map(|name| Ident::from(name))
                                    .expect("param did not have a name"),
                                ty: param.ty(),
                            }
                        })
                        .collect()
                })
                .unwrap_or_default();
            let ret_ty = f.ret();

            if !f.is_ghost() && f.body().is_none() {
                let err = TypeCheckError {
                    input: program.program(db).to_string(),
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

            Some(Item::Function(Function::new(
                db,
                f.clone(),
                name.into(),
                attrs,
                param_list,
                ret_ty,
            )))
        }
        ItemData::Struct { ast: s } => {
            let name = Ident::from(s.name().unwrap());
            let data = TypeDeclData::Struct(Struct::new(db, s.clone(), name.clone()));
            Some(Item::Type(TypeDecl::new(db, name, data)))
        }
        ItemData::TypeInvariant { ast: i } => {
            let name = Ident::from(i.name().unwrap());
            Some(Item::TypeInvariant(TypeInvariant::new(db, i.clone(), name)))
        }
        ItemData::Macro { .. } => None,
    }
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

    match item {
        Item::Type(ty_decl) => match &ty_decl.data(db) {
            TypeDeclData::Struct(_) => {
                let checker = TypeChecker::init(db, program, item_id, None);
                Some(checker.into())
            }
        },
        Item::TypeInvariant(ty_inv) => {
            let mut checker = TypeChecker::init(db, program, item_id, None);
            if let Some(ast_body) = ty_inv.node(db).block_expr() {
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
            let mut checker = TypeChecker::init(db, program, item_id, Some(function));
            let ast_body = function.syntax(db).body();
            let body = ast_body
                .as_ref()
                .map(|ast_body| checker.check_block(ast_body, |f| f));
            let is_ghost = function.attrs(db).is_ghost();
            if let Some(body) = body {
                if let Some(ret) = function.ret(db) {
                    let ret = checker
                        .find_type_src(&ret)
                        .with_ghost(is_ghost)
                        .ts(&mut checker);
                    checker.expect_ty(
                        function
                            .syntax(db)
                            .ret()
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
            if let Some(ret) = function.ret(db) {
                let ret_ty = checker.find_type_src(&ret);
                checker.set_return_ty(ret_ty);
            }
            Some(checker.into())
        }
    }
}

#[salsa::tracked]
pub fn struct_fields(db: &dyn crate::Db, s: Struct) -> Vec<Field> {
    s.node(db)
        .struct_fields()
        .map(|f| {
            let is_ghost = f.is_ghost();
            let name = f.name().unwrap();
            Field {
                parent: FieldParent::Struct(s),
                name: name.into(),
                is_ghost,
                ty: f.ty(),
            }
        })
        .collect()
}

#[salsa::interned]
pub struct ItemId {
    #[return_ref]
    pub data: ItemData,
}

impl ItemId {
    pub fn name(&self, db: &dyn crate::Db) -> Option<ast::Name> {
        self.data(db).name()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ItemData {
    Const { ast: ast::Const },
    Fn { ast: ast::Fn },
    Struct { ast: ast::Struct },
    TypeInvariant { ast: ast::TypeInvariant },
    Macro { ast: ast::Macro },
}
impl ItemData {
    fn name(&self) -> Option<ast::Name> {
        match self {
            ItemData::Const { ast } => ast.name(),
            ItemData::Fn { ast } => ast.name(),
            ItemData::Struct { ast } => ast.name(),
            ItemData::TypeInvariant { ast } => ast.name(),
            ItemData::Macro { ast } => ast.name(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

#[salsa::tracked]
pub struct Function {
    #[return_ref]
    pub syntax: mist_syntax::ast::Fn,
    #[return_ref]
    pub name: Ident,
    pub attrs: AttrFlags,
    #[return_ref]
    pub param_list: ParamList<Ident, Option<mist_syntax::ast::Type>>,
    pub ret: Option<mist_syntax::ast::Type>,
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
pub type VariableIdx = la_arena::Idx<Variable>;
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
pub struct ParamList<I, T = TypeSrcId> {
    pub params: Vec<Param<I, T>>,
}

impl<I, T> ParamList<I, T> {
    pub fn map<O>(&self, mut f: impl FnMut(&I) -> O) -> ParamList<O, T>
    where
        T: Clone,
    {
        ParamList {
            params: self
                .params
                .iter()
                .map(|param| Param {
                    is_ghost: param.is_ghost,
                    name: f(&param.name),
                    ty: param.ty.clone(),
                })
                .collect(),
        }
    }
}

impl<I, T> Default for ParamList<I, T> {
    fn default() -> Self {
        Self {
            params: Default::default(),
        }
    }
}

impl<I, T> FromIterator<Param<I, T>> for ParamList<I, T> {
    fn from_iter<Iter: IntoIterator<Item = Param<I, T>>>(iter: Iter) -> Self {
        ParamList {
            params: iter.into_iter().collect(),
        }
    }
}

impl<I, T> std::ops::Deref for ParamList<I, T> {
    type Target = [Param<I, T>];

    fn deref(&self) -> &Self::Target {
        &self.params
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Param<I, T = TypeSrcId> {
    pub is_ghost: bool,
    pub name: I,
    pub ty: T,
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

pub type ExprIdx = la_arena::Idx<Expr>;
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expr {
    pub ty: TypeId,
    pub data: ExprData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprData {
    Literal(Literal),
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
        params: ParamList<VariableIdx>,
        expr: ExprIdx,
    },
    Result,
    Range {
        lhs: Option<ExprIdx>,
        rhs: Option<ExprIdx>,
    },
    Return(Option<ExprIdx>),
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

pub type TypeSrcId = la_arena::Idx<TypeSrc>;
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeSrc {
    pub data: Option<TypeData<TypeSrcId>>,
    pub ty: TypeId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(TypeDataIdx);
pub type TypeDataIdx = la_arena::Idx<TypeData>;

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
        params: ParamList<Ident>,
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
                inner: f(&inner),
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
                attrs: attrs.clone(),
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

#[salsa::interned]
pub struct Struct {
    #[return_ref]
    node: mist_syntax::ast::Struct,
    pub name: Ident,
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
    pub ty: Option<mist_syntax::ast::Type>,
}

#[salsa::interned]
pub struct TypeInvariant {
    #[return_ref]
    node: mist_syntax::ast::TypeInvariant,
    pub name: Ident,
}

pub mod pretty {
    use super::*;
    use itertools::Itertools;

    pub trait PrettyPrint {
        fn resolve_var(&self, idx: VariableIdx) -> Ident;
        fn resolve_var_ty(&self, idx: VariableIdx) -> TypeId;
        fn resolve_ty(&self, ty: TypeId) -> TypeData;
        fn resolve_src_ty(&self, ts: TypeSrcId) -> TypeId;
        fn resolve_expr(&self, idx: ExprIdx) -> &Expr;
    }

    use expr as pp_expr;
    use params as pp_params;
    use ty as pp_ty;

    fn pp_strip_ghost(pp: &impl PrettyPrint, strip: bool, ty: TypeId) -> TypeId {
        if strip {
            match pp.resolve_ty(ty) {
                TypeData::Ghost(inner) => inner,
                _ => ty,
            }
        } else {
            ty
        }
    }

    pub fn params(
        pp: &impl PrettyPrint,
        db: &dyn crate::Db,
        strip_ghost: bool,
        params: &ParamList<Ident>,
    ) -> String {
        format!(
            "({})",
            params
                .params
                .iter()
                .map(|param| {
                    let ty = pp_strip_ghost(pp, strip_ghost, pp.resolve_src_ty(param.ty));
                    format!("{}: {}", param.name, pp_ty(pp, db, ty))
                })
                .format(", ")
        )
    }
    pub fn ty(pp: &impl PrettyPrint, db: &dyn crate::Db, ty: TypeId) -> String {
        match pp.resolve_ty(ty) {
            TypeData::Error => "Error".to_string(),
            TypeData::Void => "void".to_string(),
            TypeData::Free => "free".to_string(),
            TypeData::Ref { is_mut, inner } => {
                format!(
                    "&{}{}",
                    if is_mut { "mut " } else { "" },
                    pp_ty(pp, db, inner)
                )
            }
            TypeData::Ghost(inner) => format!("ghost {}", pp_ty(pp, db, inner)),
            TypeData::Range(inner) => format!("range {}", pp_ty(pp, db, inner)),
            TypeData::List(inner) => format!("[{}]", pp_ty(pp, db, inner)),
            TypeData::Optional(inner) => format!("?{}", pp_ty(pp, db, inner)),
            TypeData::Primitive(t) => format!("{t:?}").to_lowercase(),
            TypeData::Struct(s) => s.name(db).to_string(),
            TypeData::Null => "null".to_string(),
            TypeData::Function {
                attrs,
                name,
                params,
                return_ty,
            } => {
                let is_ghost = attrs.is_ghost();

                let mut attrs = attrs.to_string();
                if !attrs.is_empty() {
                    attrs.push(' ');
                }
                let name = name
                    .as_ref()
                    .map(|name| format!(" {name}"))
                    .unwrap_or_default();
                let params = pretty::params(pp, db, is_ghost, &params);
                let ret = if let TypeData::Void = pp.resolve_ty(pp_strip_ghost(pp, true, return_ty))
                {
                    String::new()
                } else {
                    let ty = pretty::ty(pp, db, pp_strip_ghost(pp, is_ghost, return_ty));
                    format!(" -> {ty}")
                };

                format!("{attrs}fn{name}{params}{ret}")

                //     format!(
                //     "{attrs} fn{}({}) -> {}",
                //     name.as_ref().map(|n| format!(" {n}")).unwrap_or_default(),
                //     params.iter().map(|t| pp_ty(_pp, db, *t)).format(", "),
                //     pp_ty(_pp, db, *return_ty)
                // )
            }
        }
    }
    pub fn expr(pp: &impl PrettyPrint, db: &dyn crate::Db, expr: ExprIdx) -> String {
        match &pp.resolve_expr(expr).data {
            ExprData::Literal(l) => match l {
                Literal::Null => "null".to_string(),
                Literal::Int(i) => i.to_string(),
                Literal::Bool(b) => b.to_string(),
            },
            ExprData::Ident(i) => pp.resolve_var(i.idx).to_string(),
            ExprData::Field {
                expr, field_name, ..
            } => format!("{}.{field_name}", pp_expr(pp, db, *expr)),
            ExprData::Struct {
                struct_declaration,
                fields,
                ..
            } => format!(
                "{} {{ {} }}",
                struct_declaration.name(db),
                fields
                    .iter()
                    .map(|f| format!("{}: {}", f.name, pp_expr(pp, db, f.value)))
                    .format(", ")
            ),
            ExprData::Missing => "<missing>".to_string(),
            ExprData::If(it) => format!("if {}", pp_expr(pp, db, it.condition)),
            ExprData::Block(_block) => "<block>".to_string(),
            ExprData::Return(Some(e)) => format!("return {}", pp_expr(pp, db, *e)),
            ExprData::Return(None) => "return".to_string(),
            ExprData::Call { expr, args } => format!(
                "{}({})",
                pp_expr(pp, db, *expr),
                args.iter().map(|arg| pp_expr(pp, db, *arg)).format(", ")
            ),
            ExprData::Unary { op, inner } => {
                format!("({op} {})", pp_expr(pp, db, *inner))
            }
            ExprData::Bin { lhs, op, rhs } => {
                format!("({} {op} {})", pp_expr(pp, db, *lhs), pp_expr(pp, db, *rhs))
            }
            &ExprData::Range { lhs, rhs } => {
                format!(
                    "{}..{}",
                    lhs.map(|e| pp_expr(pp, db, e)).unwrap_or_default(),
                    rhs.map(|e| pp_expr(pp, db, e)).unwrap_or_default()
                )
            }
            &ExprData::Index { base, index } => {
                format!("{}[{}]", pp_expr(pp, db, base), pp_expr(pp, db, index))
            }
            ExprData::List { elems } => format!(
                "[{}]",
                elems.iter().map(|e| pp_expr(pp, db, *e)).format(", ")
            ),
            ExprData::Ref { is_mut, expr } => {
                format!(
                    "&{}{}",
                    if *is_mut { "mut" } else { "" },
                    pp_expr(pp, db, *expr)
                )
            }
            ExprData::Quantifier {
                quantifier,
                params,
                expr,
            } => format!(
                "{quantifier}{} {{ {} }}",
                pp_params(pp, db, true, &params.map(|var| pp.resolve_var(*var))),
                pp_expr(pp, db, *expr)
            ),
            ExprData::Result => "result".to_string(),
        }
    }
}
