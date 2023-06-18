use mist_syntax::ast::{
    self,
    operators::{BinaryOp, UnaryOp},
};

use crate::{
    def::Def,
    hir::{self, ExprIdx, Literal, Quantifier, SpanOrAstPtr, StatementId, VariableIdx},
};

use super::{
    lower::MonoDefLower,
    types::{Adt, AdtField, Type},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprPtr {
    pub(super) def: Def,
    pub(super) id: ExprIdx,
    pub(super) ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VariablePtr {
    pub(super) def: Def,
    pub(super) id: VariableIdx,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprData {
    Literal(Literal),
    Self_,
    Ident(VariablePtr),
    Field { expr: ExprPtr, field: Field },
    Adt { adt: Adt, fields: Vec<(AdtField, ExprPtr)> },
    Missing,
    Block(Block),
    If(IfExpr),
    While(WhileExpr),
    For(ForExpr),
    Call { expr: ExprPtr, args: Vec<ExprPtr> },
    Unary { op: UnaryOp, inner: ExprPtr },
    Bin { lhs: ExprPtr, op: BinaryOp, rhs: ExprPtr },
    Ref { is_mut: bool, expr: ExprPtr },
    Index { base: ExprPtr, index: ExprPtr },
    List { elems: Vec<ExprPtr> },
    Quantifier { quantifier: Quantifier, over: QuantifierOver, expr: ExprPtr },
    Result,
    Range { lhs: Option<ExprPtr>, rhs: Option<ExprPtr> },
    Return(Option<ExprPtr>),
    NotNull(ExprPtr),
    Builtin(BuiltinExpr),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Field {
    Builtin,
    AdtField(Adt, AdtField),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum QuantifierOver {
    Vars(Vec<VariablePtr>),
    In(VariablePtr, ExprPtr),
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BuiltinExpr {
    RangeMin(ExprPtr),
    RangeMax(ExprPtr),
    InRange(ExprPtr, ExprPtr),
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    pub stmts: Vec<StatementId>,
    pub tail_expr: Option<ExprPtr>,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IfExpr {
    pub condition: ExprPtr,
    pub then_branch: ExprPtr,
    pub else_branch: Option<ExprPtr>,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ForExpr {
    pub is_ghost: bool,
    pub variable: VariablePtr,
    pub in_expr: ExprPtr,
    pub invariants: Vec<Vec<ExprPtr>>,
    pub body: ExprPtr,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WhileExpr {
    pub expr: ExprPtr,
    pub invariants: Vec<Vec<ExprPtr>>,
    pub decreases: Decreases,
    pub body: ExprPtr,
}
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Decreases {
    #[default]
    Unspecified,
    Expr(ExprPtr),
    Inferred,
}

impl ExprPtr {
    pub fn ast(&self, db: &dyn crate::Db) -> SpanOrAstPtr<ast::Expr> {
        let hir = self.def.hir(db).unwrap();
        hir.source_map(db).expr_src(hir.cx(db), self.id)
    }
    pub fn id(&self) -> (Def, ExprIdx) {
        (self.def, self.id)
    }
    pub fn data(&self, db: &dyn crate::Db) -> ExprData {
        let cx = self.def.hir(db).unwrap().cx(db);
        let mut mdl = MonoDefLower::new(db, cx);

        let expr = cx.expr(self.id);

        match &expr.data {
            hir::ExprData::Literal(_) => todo!(),
            hir::ExprData::Self_ => todo!(),
            hir::ExprData::Ident(_) => todo!(),
            hir::ExprData::Block(_) => todo!(),
            hir::ExprData::Field { expr, field } => todo!(),
            hir::ExprData::Adt { adt, fields } => todo!(),
            hir::ExprData::Missing => todo!(),
            hir::ExprData::If(_) => todo!(),
            hir::ExprData::While(_) => todo!(),
            hir::ExprData::For(_) => todo!(),
            hir::ExprData::Call { expr, args } => todo!(),
            hir::ExprData::Unary { op, inner } => todo!(),
            hir::ExprData::Bin { lhs, op, rhs } => todo!(),
            hir::ExprData::Ref { is_mut, expr } => todo!(),
            hir::ExprData::Index { base, index } => todo!(),
            hir::ExprData::List { elems } => {
                ExprData::List { elems: elems.iter().map(|&id| mdl.lower_expr(id)).collect() }
            }
            hir::ExprData::Quantifier { quantifier, over, expr } => todo!(),
            hir::ExprData::Result => todo!(),
            hir::ExprData::Range { lhs, rhs } => todo!(),
            hir::ExprData::Return(_) => todo!(),
            hir::ExprData::NotNull(_) => todo!(),
            hir::ExprData::Builtin(_) => todo!(),
        }
    }
}
