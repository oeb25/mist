use derive_more::Display;
use derive_new::new;
use mist_syntax::ast::{
    self,
    operators::{BinaryOp, UnaryOp},
    AttrFlags,
};

use crate::{
    def::{Name, Struct, StructField},
    types::{Adt, Field, Primitive, TypeId},
    util::impl_idx,
};

use super::ItemSourceMap;

#[salsa::interned]
pub struct Variable {
    pub name: Name,
    pub ty_src: TypeSrc,
}
impl_idx!(VariableIdx, Variable, default_debug);
impl Variable {
    pub fn ty(&self, db: &dyn crate::Db) -> TypeId {
        self.ty_src(db).ty(db)
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Param<I, T> {
    pub is_ghost: bool,
    pub name: I,
    pub ty: T,
}

impl<I, T> Param<I, T> {
    pub fn map_name<J>(&self, f: impl FnOnce(&I) -> J) -> Param<J, T>
    where
        T: Clone,
    {
        Param { is_ghost: self.is_ghost, name: f(&self.name), ty: self.ty.clone() }
    }
    pub fn map_ty<S>(&self, f: impl FnOnce(&T) -> S) -> Param<I, S>
    where
        I: Clone,
    {
        Param { is_ghost: self.is_ghost, name: self.name.clone(), ty: f(&self.ty) }
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expr {
    pub ty: TypeId,
    pub data: ExprData,
}
impl Expr {
    pub(super) fn new_block(block: Block) -> Expr {
        Expr { ty: block.return_ty, data: ExprData::Block(block) }
    }
    pub(super) fn new_if(if_expr: IfExpr) -> Expr {
        Expr { ty: if_expr.return_ty, data: ExprData::If(if_expr) }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprData {
    Literal(Literal),
    Self_,
    Ident(VariableIdx),
    Block(Block),
    Field { expr: ExprIdx, field: Field },
    Adt { adt: Adt, fields: Vec<StructExprField> },
    Missing,
    If(IfExpr),
    While(WhileExpr),
    For(ForExpr),
    Call { expr: ExprIdx, args: Vec<ExprIdx> },
    Unary { op: UnaryOp, inner: ExprIdx },
    Bin { lhs: ExprIdx, op: BinaryOp, rhs: ExprIdx },
    Ref { is_mut: bool, expr: ExprIdx },
    Index { base: ExprIdx, index: ExprIdx },
    List { elems: Vec<ExprIdx> },
    Quantifier { quantifier: Quantifier, over: QuantifierOver, expr: ExprIdx },
    Result,
    Range { lhs: Option<ExprIdx>, rhs: Option<ExprIdx> },
    Return(Option<ExprIdx>),
    NotNull(ExprIdx),
    Builtin(BuiltinExpr),
}
impl ExprData {
    pub(super) fn typed(self, ty: TypeId) -> Expr {
        Expr { ty, data: self }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum QuantifierOver {
    Vars(Vec<VariableIdx>),
    In(VariableIdx, ExprIdx),
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BuiltinExpr {
    RangeMin(ExprIdx),
    RangeMax(ExprIdx),
    InRange(ExprIdx, ExprIdx),
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

#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Quantifier {
    #[display(fmt = "forall")]
    Forall,
    #[display(fmt = "exists")]
    Exists,
}
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructExprField {
    pub decl: StructField,
    pub value: ExprIdx,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IfExpr {
    pub is_ghost: bool,
    pub return_ty: TypeId,
    pub condition: ExprIdx,
    pub then_branch: ExprIdx,
    pub else_branch: Option<ExprIdx>,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ForExpr {
    pub is_ghost: bool,
    pub variable: VariableIdx,
    pub in_expr: ExprIdx,
    pub invariants: Vec<Vec<ExprIdx>>,
    pub body: ExprIdx,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WhileExpr {
    pub expr: ExprIdx,
    pub invariants: Vec<Vec<ExprIdx>>,
    pub decreases: Decreases,
    pub body: ExprIdx,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    pub stmts: Vec<StatementId>,
    pub tail_expr: Option<ExprIdx>,
    pub return_ty: TypeId,
}

impl_idx!(StatementId, Statement, default_debug);
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Statement {
    pub data: StatementData,
}

impl Statement {
    pub fn new(data: StatementData) -> Self {
        Self { data }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Let {
    pub variable: VariableIdx,
    pub initializer: ExprIdx,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StatementData {
    Expr(ExprIdx),
    Let(Let),
    Assertion { kind: AssertionKind, exprs: Vec<ExprIdx> },
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Path {
    Name(Name),
    Struct(Struct),
}

/// A unique explicit type with origin in a source file. One of these should be
/// instantiated for each type in a source file. It's actual representation is
/// interned in [`TypeRef`].
#[salsa::tracked]
pub struct TypeSrc {
    data: Option<TypeRef>,
    pub ty: TypeId,
}

/// An interned explicit type, as written in a source file. Instances of
/// [`TypeRef`] are not unique, and cannot be used to rely on to track source
/// locations. To do so, use [`TypeSrc`].
#[salsa::interned]
pub struct TypeRef {
    #[salsa(return_ref)]
    pub data: TypeRefKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeRefKind {
    Error,
    Void,
    Ref {
        is_mut: bool,
        inner: Box<TypeRefKind>,
    },
    List(Box<TypeRefKind>),
    Optional(Box<TypeRefKind>),
    Ghost(Box<TypeRefKind>),
    Primitive(Primitive),
    Path(Path),
    Null,
    Function {
        attrs: AttrFlags,
        name: Option<Name>,
        params: Vec<Param<Name, TypeRefKind>>,
        return_ty: Box<TypeRefKind>,
    },
    Range(Box<TypeRefKind>),
}

impl TypeSrc {
    pub fn sourced(db: &dyn crate::Db, data: TypeRef, ty: TypeId) -> TypeSrc {
        TypeSrc::new(db, Some(data), ty)
    }
    pub fn unsourced(db: &dyn crate::Db, ty: TypeId) -> TypeSrc {
        TypeSrc::new(db, None, ty)
    }
    pub fn type_ref(self, db: &dyn crate::Db) -> Option<TypeRefKind> {
        self.data(db).map(|it| it.data(db))
    }
}

impl Let {
    pub fn explicit_ty(&self, ast: &ast::LetStmt, source_map: &ItemSourceMap) -> Option<TypeSrc> {
        source_map.ty_ast((&ast.ty()?).into())
    }
}
