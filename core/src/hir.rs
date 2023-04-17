mod lower;

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

pub use crate::typecheck::{ItemContext, ItemSourceMap};
use crate::{
    typecheck::{self, TypeCheckError, TypeCheckErrorKind, TypeCheckExpr},
    TypeCheckErrors,
};

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
            ast::Item::Const(node) => ItemId::Const { ast: node },
            ast::Item::Fn(node) => ItemId::Fn { ast: node },
            ast::Item::Struct(node) => ItemId::Struct { ast: node },
            ast::Item::TypeInvariant(node) => ItemId::TypeInvariant { ast: node },
            ast::Item::Macro(node) => ItemId::Macro { ast: node },
        })
        .collect();
    Program::new(db, program, items, errors)
}

#[salsa::tracked]
pub fn item(db: &dyn crate::Db, program: Program, item: ItemId) -> Option<Item> {
    match item {
        ItemId::Const { .. } => None,
        ItemId::Fn { ast: f } => {
            let name = if let Some(name) = f.name() {
                name
            } else {
                todo!()
            };
            let attrs = f.attr_flags();
            let param_list = typecheck::check_param_list(db, program, f.param_list());
            let ret_ty = f.ret().map(|ty| find_type(db, program, ty));

            match &ret_ty {
                Some(ty) if !f.is_ghost() && ty.is_ghost(db) => {
                    let err = TypeCheckError {
                        input: program.program(db).to_string(),
                        span: f.ret().unwrap().span(),
                        label: None,
                        help: None,
                        kind: TypeCheckErrorKind::GhostUsedInNonGhost,
                    };
                    TypeCheckErrors::push(db, err);
                }
                _ => {}
            }

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
                f,
                name.into(),
                attrs,
                param_list,
                ret_ty,
            )))
        }
        ItemId::Struct { ast: s } => {
            let name = Ident::from(s.name().unwrap());
            let data = TypeDeclData::Struct(Struct::new(db, s, name.clone()));
            Some(Item::Type(TypeDecl::new(db, name, data)))
        }
        ItemId::TypeInvariant { ast: i } => {
            let name = Ident::from(i.name().unwrap());
            Some(Item::TypeInvariant(TypeInvariant::new(db, i, name)))
        }
        ItemId::Macro { .. } => None,
    }
}

#[salsa::tracked]
pub fn item_lower(
    db: &dyn crate::Db,
    program: Program,
    item: Item,
) -> Option<(ItemContext, ItemSourceMap)> {
    match item {
        Item::Type(_) => None,
        Item::TypeInvariant(ty_inv) => {
            let mut checker = TypeCheckExpr::init(db, program, None);
            if let Some(ast_body) = ty_inv.node(db).block_expr() {
                let body = checker.check_block(&ast_body, |f| f);
                checker.expect_ty(
                    ty_inv.name(db).span(),
                    Type::bool(db).ghost(db),
                    body.return_ty,
                );
                checker.set_body_expr_from_block(body, ast_body);
            }
            Some(checker.into())
        }
        Item::Function(function) => {
            let mut checker = TypeCheckExpr::init(db, program, Some(function));
            let ast_body = function.syntax(db).body();
            let body = ast_body
                .as_ref()
                .map(|ast_body| checker.check_block(ast_body, |f| f));
            let is_ghost = function.attrs(db).is_ghost();
            if let Some(body) = body {
                if let Some(ret) = function.ret(db) {
                    let ret = ret.with_ghost(db, is_ghost);
                    checker.expect_ty(
                        function
                            .syntax(db)
                            .ret()
                            .map(|ret| ret.span())
                            .unwrap_or_else(|| function.name(db).span()),
                        ret,
                        body.return_ty,
                    );
                } else {
                    checker.expect_ty(
                        function.name(db).span(),
                        Type::void(db).with_ghost(db, is_ghost),
                        body.return_ty,
                    );
                }
                checker.set_body_expr_from_block(body, ast_body.unwrap());
            }
            Some(checker.into())
        }
    }
}

#[salsa::tracked]
pub fn struct_fields(db: &dyn crate::Db, program: Program, s: Struct) -> Vec<Field> {
    s.node(db)
        .struct_fields()
        .map(|f| {
            let is_ghost = f.is_ghost();
            let name = f.name().unwrap();
            Field {
                parent: FieldParent::Struct(s),
                name: name.into(),
                is_ghost,
                ty: if let Some(ty) = f.ty() {
                    find_type(db, program, ty).with_ghost(db, is_ghost)
                } else {
                    Type::error(db)
                },
            }
        })
        .collect()
}

#[salsa::tracked]
pub fn struct_ty(db: &dyn crate::Db, s: Struct, reference_span: SourceSpan) -> Type {
    Type::new(db, TypeData::Struct(s), Some(reference_span))
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ItemId {
    Const { ast: ast::Const },
    Fn { ast: ast::Fn },
    Struct { ast: ast::Struct },
    TypeInvariant { ast: ast::TypeInvariant },
    Macro { ast: ast::Macro },
}
impl ItemId {
    fn name(&self) -> Option<ast::Name> {
        match self {
            ItemId::Const { ast } => ast.name(),
            ItemId::Fn { ast } => ast.name(),
            ItemId::Struct { ast } => ast.name(),
            ItemId::TypeInvariant { ast } => ast.name(),
            ItemId::Macro { ast } => ast.name(),
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
    pub param_list: ParamList<Ident>,
    pub ret: Option<Type>,
}

#[salsa::tracked]
pub fn find_named_type(db: &dyn crate::Db, program: Program, name: Ident) -> Type {
    for item in program.items(db) {
        let item_name = item.name().map(|n| n.to_string());
        if item_name.as_deref() == Some(&name) {
            match item {
                ItemId::Struct { ast } => {
                    let item_name = ast.name().unwrap();
                    let s = Struct::new(db, ast.clone(), item_name.into());
                    return struct_ty(db, s, name.span());
                }
                ItemId::Const { .. }
                | ItemId::Fn { .. }
                | ItemId::TypeInvariant { .. }
                | ItemId::Macro { .. } => return Type::error(db),
            }
        }
    }

    let err = TypeCheckError {
        input: program.program(db).to_string(),
        span: name.span(),
        label: None,
        help: None,
        kind: TypeCheckErrorKind::UndefinedType(name.to_string()),
    };
    TypeCheckErrors::push(db, err);

    Type::new(db, TypeData::Error, Some(name.span()))
}
#[salsa::tracked]
pub fn find_type(db: &dyn crate::Db, program: Program, ty: mist_syntax::ast::Type) -> Type {
    let result = match &ty {
        mist_syntax::ast::Type::NamedType(name) => {
            let name = name.name().unwrap().into();
            return find_named_type(db, program, name);
        }
        mist_syntax::ast::Type::Primitive(it) => match () {
            _ if it.int_token().is_some() => TypeData::Primitive(Primitive::Int),
            _ if it.bool_token().is_some() => TypeData::Primitive(Primitive::Bool),
            _ => {
                todo!();
                // TypeData::Error
            }
        },
        mist_syntax::ast::Type::Optional(it) => {
            if let Some(ty) = it.ty() {
                let inner = find_type(db, program, ty);
                TypeData::Optional(inner)
            } else {
                todo!()
            }
        }
        mist_syntax::ast::Type::RefType(r) => {
            let is_mut = r.mut_token().is_some();

            if let Some(ty) = r.ty() {
                let inner = find_type(db, program, ty);
                TypeData::Ref { is_mut, inner }
            } else {
                let err = TypeCheckError {
                    input: program.program(db).to_string(),
                    span: r.span(),
                    label: None,
                    help: None,
                    kind: TypeCheckErrorKind::UndefinedType("what is this".to_string()),
                };
                eprintln!("{:?}", miette::Error::new(err));

                TypeData::Ref {
                    is_mut,
                    inner: Type::error(db),
                }
            }
        }
        mist_syntax::ast::Type::ListType(t) => {
            if let Some(ty) = t.ty() {
                let inner = find_type(db, program, ty);
                TypeData::List(inner)
            } else {
                let err = TypeCheckError {
                    input: program.program(db).to_string(),
                    span: t.span(),
                    label: None,
                    help: None,
                    kind: TypeCheckErrorKind::UndefinedType("list of what".to_string()),
                };
                eprintln!("{:?}", miette::Error::new(err));
                return Type::error(db);
            }
        }
        mist_syntax::ast::Type::GhostType(t) => {
            if let Some(ty) = t.ty() {
                let inner = find_type(db, program, ty);
                TypeData::Ghost(inner)
            } else {
                let err = TypeCheckError {
                    input: program.program(db).to_string(),
                    span: t.span(),
                    label: None,
                    help: None,
                    kind: TypeCheckErrorKind::UndefinedType("ghost of what".to_string()),
                };
                eprintln!("{:?}", miette::Error::new(err));
                return Type::error(db);
            }
        }
    };

    Type::new(db, result, Some(ty.span()))
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
pub struct ParamList<I> {
    pub params: Vec<Param<I>>,
}

impl<I> ParamList<I> {
    pub fn map<O>(&self, mut f: impl FnMut(&I) -> O) -> ParamList<O> {
        ParamList {
            params: self
                .params
                .iter()
                .map(|param| Param {
                    is_ghost: param.is_ghost,
                    name: f(&param.name),
                    ty: param.ty,
                })
                .collect(),
        }
    }
}

impl<I> Default for ParamList<I> {
    fn default() -> Self {
        Self {
            params: Default::default(),
        }
    }
}

impl<I> FromIterator<Param<I>> for ParamList<I> {
    fn from_iter<T: IntoIterator<Item = Param<I>>>(iter: T) -> Self {
        ParamList {
            params: iter.into_iter().collect(),
        }
    }
}

impl<I> std::ops::Deref for ParamList<I> {
    type Target = [Param<I>];

    fn deref(&self) -> &Self::Target {
        &self.params
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Param<I> {
    pub is_ghost: bool,
    pub name: I,
    pub ty: Type,
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
    pub ty: Type,
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
    pub return_ty: Type,
    pub condition: ExprIdx,
    pub then_branch: Block,
    pub else_branch: Option<Box<Else>>,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Else {
    If(IfExpr),
    Block(Block),
}
impl Else {
    pub fn first_block(&self) -> &Block {
        match self {
            Else::If(it) => &it.then_branch,
            Else::Block(it) => it,
        }
    }
    pub fn return_ty(&self, _db: &dyn crate::Db) -> Type {
        match self {
            Else::If(it) => it.return_ty,
            Else::Block(it) => it.return_ty,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    pub stmts: Vec<Statement>,
    pub tail_expr: Option<ExprIdx>,
    pub return_ty: Type,
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
        explicit_ty: Option<Type>,
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

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
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

#[salsa::interned]
pub struct Type {
    #[return_ref]
    pub data: TypeData,
    pub span: Option<SourceSpan>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeData {
    Error,
    Void,
    Ghost(Type),
    Ref {
        is_mut: bool,
        inner: Type,
    },
    List(Type),
    Optional(Type),
    Primitive(Primitive),
    Struct(Struct),
    Null,
    Function {
        attrs: AttrFlags,
        name: Option<Ident>,
        params: ParamList<Ident>,
        return_ty: Type,
    },
    Range(Type),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Primitive {
    Int,
    Bool,
}

impl Type {
    pub(crate) fn ghost(self, db: &dyn crate::Db) -> Self {
        match self.data(db) {
            TypeData::Ghost(_) => self,
            _ => Type::new(db, TypeData::Ghost(self), self.span(db)),
        }
    }
    pub(crate) fn with_ghost(self, db: &dyn crate::Db, ghost: bool) -> Self {
        if ghost {
            self.ghost(db)
        } else {
            self
        }
    }
    pub fn strip_ghost(self, db: &dyn crate::Db) -> Self {
        match self.data(db) {
            TypeData::Ghost(inner) => inner.strip_ghost(db),
            _ => self,
        }
    }
    pub fn is_ghost(self, db: &dyn crate::Db) -> bool {
        match self.data(db) {
            TypeData::Ghost(_) => true,
            // TODO: Should we recurse and check if non of the children are ghost?
            _ => false,
        }
    }
    #[allow(unused)]
    pub(crate) fn with_span(self, db: &dyn crate::Db, span: SourceSpan) -> Self {
        Type::new(db, self.data(db).clone(), Some(span))
    }
    pub(crate) fn without_span(self, db: &dyn crate::Db) -> Self {
        Type::new(db, self.data(db).clone(), None)
    }
}

#[salsa::interned]
pub struct Struct {
    #[return_ref]
    node: mist_syntax::ast::Struct,
    pub name: Ident,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FieldParent {
    Struct(Struct),
    List(Type),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Field {
    pub parent: FieldParent,
    pub name: Ident,
    pub is_ghost: bool,
    pub ty: Type,
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
        fn resolve_var_ty(&self, idx: VariableIdx) -> Type;
        fn resolve_expr(&self, idx: ExprIdx) -> &Expr;
    }

    use expr as pp_expr;
    use params as pp_params;
    use ty as pp_ty;

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
                .map(|param| format!(
                    "{}: {}",
                    param.name,
                    pp_ty(
                        pp,
                        db,
                        if strip_ghost {
                            param.ty.strip_ghost(db)
                        } else {
                            param.ty
                        }
                    )
                ))
                .format(", ")
        )
    }
    pub fn ty(pp: &impl PrettyPrint, db: &dyn crate::Db, ty: Type) -> String {
        match ty.data(db) {
            TypeData::Error => "Error".to_string(),
            TypeData::Void => "void".to_string(),
            &TypeData::Ref { is_mut, inner } => {
                format!(
                    "&{}{}",
                    if is_mut { "mut " } else { "" },
                    pp_ty(pp, db, inner)
                )
            }
            &TypeData::Ghost(inner) => format!("ghost {}", pp_ty(pp, db, inner)),
            &TypeData::Range(inner) => format!("range {}", pp_ty(pp, db, inner)),
            &TypeData::List(inner) => format!("[{}]", pp_ty(pp, db, inner)),
            &TypeData::Optional(inner) => format!("{}?", pp_ty(pp, db, inner)),
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
                let params = pretty::params(pp, db, is_ghost, params);
                let ret = if let TypeData::Void = return_ty.strip_ghost(db).data(db) {
                    String::new()
                } else {
                    let ty = pretty::ty(
                        pp,
                        db,
                        if is_ghost {
                            return_ty.strip_ghost(db)
                        } else {
                            *return_ty
                        },
                    );
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
