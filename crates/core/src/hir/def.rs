mod name;

use derive_more::Display;
use derive_new::new;
use mist_syntax::{
    ast::{
        self,
        operators::{BinaryOp, UnaryOp},
    },
    ptr::AstPtr,
    SourceSpan,
};

use crate::{
    def::{Struct, StructField},
    types::{Field, TypeData, TypeId},
    util::impl_idx,
};

pub use name::Name;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Variable {}
impl Variable {
    pub fn new() -> Variable {
        Variable {}
    }
}
impl Default for Variable {
    fn default() -> Self {
        Self::new()
    }
}
impl_idx!(VariableIdx, Variable, default_debug);
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
        Param { is_ghost: self.is_ghost, name: f(&self.name), ty: self.ty.clone() }
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
    Field { expr: ExprIdx, field_name: Name, field: Field },
    Struct { struct_declaration: Struct, struct_span: SourceSpan, fields: Vec<StructExprField> },
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
    Params(Vec<Param<VariableIdx>>),
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
    pub decl: StructField,
    // TODO: remove this as it could be computed using the source map
    pub name: AstPtr<ast::NameRef>,
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
    Let { variable: VariableIdx, explicit_ty: Option<TypeSrcId>, initializer: ExprIdx },
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

impl_idx!(TypeSrcId, TypeSrc, default_debug);
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeSrc {
    pub data: Option<TypeData<TypeSrcId>>,
    pub ty: TypeId,
}
