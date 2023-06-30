use itertools::Either;
use mist_syntax::ast::{
    self,
    operators::{BinaryOp, UnaryOp},
};

use crate::{
    def::{Def, Name},
    hir::{
        self, AssertionKind, ExprIdx, Literal, Quantifier, SpanOrAstPtr, StatementId, VariableIdx,
    },
    types::BuiltinField,
};

use super::{
    lower::MonoDefLower,
    types::{Adt, AdtField, Type},
    Function,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprPtr {
    pub(super) def: Def,
    pub(super) id: ExprIdx,
    pub(super) ty: Type,
    pub(super) inner_data: ExprDataWrapper,
}
#[salsa::interned]
pub(crate) struct ExprDataWrapper {
    data: ExprData,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VariablePtr {
    pub(super) def: Def,
    pub(super) id: VariableIdx,
    pub(super) ty: Type,
    pub(super) decl: Option<VariableDeclaration>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VariableDeclaration {
    Function(Function),
    Let { is_mut: bool },
    Parameter,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StatementPtr {
    pub(super) def: Def,
    pub(super) id: StatementId,
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
    Call { fun: ExprFunction, args: Vec<ExprPtr> },
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExprFunction {
    Expr(ExprPtr),
    Builtin(BuiltinField<Type>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Field {
    Undefined,
    AdtField(Adt, AdtField),
    Builtin(BuiltinField<Type>),
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
    pub stmts: Vec<StatementPtr>,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StatementData {
    Expr(ExprPtr),
    Let(Let),
    Assertion { kind: AssertionKind, exprs: Vec<ExprPtr> },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Let {
    pub variable: Option<VariablePtr>,
    pub initializer: ExprPtr,
}

impl ExprPtr {
    pub fn ast(&self, db: &dyn crate::Db) -> SpanOrAstPtr<ast::Expr> {
        let hir = self.def.hir(db).unwrap();
        hir.source_map(db).expr_src(hir.cx(db), self.id)
    }
    pub fn id(&self) -> (Def, ExprIdx) {
        (self.def, self.id)
    }
    pub fn ty(&self) -> Type {
        self.ty
    }
    pub fn data(&self, db: &dyn crate::Db) -> ExprData {
        self.inner_data.data(db)
    }
    pub fn visit(self, db: &dyn crate::Db, f: &mut impl FnMut(Either<ExprPtr, StatementPtr>)) {
        use Either::*;

        f(Left(self));
        match self.data(db) {
            ExprData::Literal(_) => {}
            ExprData::Self_ => {}
            ExprData::Ident(_) => {}
            ExprData::Field { expr, .. } => expr.visit(db, f),
            ExprData::Adt { fields, .. } => {
                for (_, expr) in fields {
                    expr.visit(db, f);
                }
            }
            ExprData::Missing => {}
            ExprData::Block(b) => {
                for stmt in b.stmts {
                    stmt.visit(db, f);
                }
                if let Some(expr) = b.tail_expr {
                    expr.visit(db, f);
                }
            }
            ExprData::If(it) => {
                it.condition.visit(db, f);
                it.then_branch.visit(db, f);
                if let Some(e) = it.else_branch {
                    e.visit(db, f)
                }
            }
            ExprData::While(it) => {
                it.expr.visit(db, f);
                for invs in it.invariants {
                    for inv in invs {
                        inv.visit(db, f);
                    }
                }
                match it.decreases {
                    Decreases::Expr(e) => e.visit(db, f),
                    Decreases::Unspecified | Decreases::Inferred => {}
                }
                it.body.visit(db, f);
            }
            ExprData::For(it) => {
                it.in_expr.visit(db, f);
                for invs in it.invariants {
                    for inv in invs {
                        inv.visit(db, f);
                    }
                }
                it.body.visit(db, f);
            }
            ExprData::Call { fun, args } => {
                match fun {
                    ExprFunction::Expr(expr) => expr.visit(db, f),
                    ExprFunction::Builtin(_) => {}
                }
                for arg in args {
                    arg.visit(db, f);
                }
            }
            ExprData::Unary { inner, .. } => {
                inner.visit(db, f);
            }
            ExprData::Bin { lhs, rhs, .. } => {
                lhs.visit(db, f);
                rhs.visit(db, f);
            }
            ExprData::Ref { expr, .. } => {
                expr.visit(db, f);
            }
            ExprData::Index { base, index } => {
                base.visit(db, f);
                index.visit(db, f);
            }
            ExprData::List { elems } => {
                for elem in elems {
                    elem.visit(db, f);
                }
            }
            ExprData::Quantifier { over, expr, .. } => {
                match over {
                    QuantifierOver::In(_, e) => e.visit(db, f),
                    QuantifierOver::Vars(_) => {}
                }
                expr.visit(db, f);
            }
            ExprData::Result => {}
            ExprData::Range { lhs, rhs } => {
                if let Some(lhs) = lhs {
                    lhs.visit(db, f);
                }
                if let Some(rhs) = rhs {
                    rhs.visit(db, f);
                }
            }
            ExprData::Return(expr) => {
                if let Some(e) = expr {
                    e.visit(db, f)
                }
            }
            ExprData::NotNull(e) => e.visit(db, f),
            ExprData::Builtin(b) => match b {
                BuiltinExpr::RangeMin(expr) | BuiltinExpr::RangeMax(expr) => expr.visit(db, f),
                BuiltinExpr::InRange(a, b) => {
                    a.visit(db, f);
                    b.visit(db, f);
                }
            },
        }
    }
}

impl VariablePtr {
    pub fn id(&self) -> (Def, VariableIdx) {
        (self.def, self.id)
    }
    pub fn ty(&self) -> Type {
        self.ty
    }
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        self.def.hir(db).unwrap().cx(db).var_name(self.id)
    }
}

impl StatementPtr {
    pub fn id(&self) -> (Def, StatementId) {
        (self.def, self.id)
    }
    pub fn data(&self, db: &dyn crate::Db) -> StatementData {
        let cx = self.def.hir(db).unwrap().cx(db);
        let mut mdl = MonoDefLower::new(db, cx);

        match &cx[self.id].data {
            hir::StatementData::Expr(expr) => StatementData::Expr(mdl.lower_expr(*expr)),
            hir::StatementData::Let(it) => StatementData::Let(Let {
                variable: it.variable.map(|var| mdl.lower_var(var)),
                initializer: mdl.lower_expr(it.initializer),
            }),
            hir::StatementData::Assertion { kind, exprs } => StatementData::Assertion {
                kind: *kind,
                exprs: exprs.iter().map(|expr| mdl.lower_expr(*expr)).collect(),
            },
        }
    }
    pub fn visit(self, db: &dyn crate::Db, f: &mut impl FnMut(Either<ExprPtr, StatementPtr>)) {
        use Either::*;

        f(Right(self));
        match self.data(db) {
            StatementData::Expr(expr) => expr.visit(db, f),
            StatementData::Let(it) => {
                it.initializer.visit(db, f);
            }
            StatementData::Assertion { exprs, .. } => {
                for expr in exprs {
                    expr.visit(db, f)
                }
            }
        }
    }
}

impl Field {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        match self {
            Field::Undefined => Name::new("<undefined field>"),
            Field::AdtField(_, f) => f.name(db),
            Field::Builtin(bf) => bf.name(),
        }
    }
    pub fn from_adt_field(db: &dyn crate::Db, adt_field: AdtField) -> Field {
        Field::AdtField(adt_field.adt(db), adt_field)
    }
}
