mod name;

use derive_more::Display;
use derive_new::new;
use mist_syntax::{
    ast::{
        self,
        operators::{BinaryOp, UnaryOp},
        Spanned,
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
#[salsa::interned]
pub struct VariableId {
    #[return_ref]
    pub text: Name,
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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expr {
    pub ty: TypeId,
    pub data: ExprData,
}
impl Expr {
    pub(super) fn new_block(block: Block) -> Expr {
        Expr {
            ty: block.return_ty,
            data: ExprData::Block(block),
        }
    }
    pub(super) fn new_if(if_expr: IfExpr) -> Expr {
        Expr {
            ty: if_expr.return_ty,
            data: ExprData::If(if_expr),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprData {
    Literal(Literal),
    Self_,
    Ident(VariableRef),
    Block(Block),
    Field {
        expr: ExprIdx,
        field_name: Name,
        field: Field,
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
impl ExprData {
    pub(super) fn typed(self, ty: TypeId) -> Expr {
        Expr { ty, data: self }
    }
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
