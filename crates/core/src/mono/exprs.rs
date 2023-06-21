use mist_syntax::ast::{
    self,
    operators::{BinaryOp, UnaryOp},
};

use crate::{
    def::{Def, Name},
    hir::{
        self, AssertionKind, ExprIdx, Literal, Quantifier, SpanOrAstPtr, StatementId, VariableIdx,
    },
    types::ListField,
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
    pub(super) ty: Type,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Field {
    Undefined,
    AdtField(Adt, AdtField),
    List(Type, ListField),
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
        let cx = self.def.hir(db).unwrap().cx(db);
        let mut mdl = MonoDefLower::new(db, cx);

        let expr = cx.expr(self.id);

        match &expr.data {
            hir::ExprData::Literal(it) => ExprData::Literal(it.clone()),
            hir::ExprData::Self_ => ExprData::Self_,
            hir::ExprData::Ident(var) => ExprData::Ident(mdl.lower_var(*var)),
            hir::ExprData::Block(it) => ExprData::Block(Block {
                stmts: it
                    .stmts
                    .iter()
                    .map(|stmt| StatementPtr { def: self.def, id: *stmt })
                    .collect(),
                tail_expr: it.tail_expr.map(|expr| mdl.lower_expr(expr)),
            }),
            hir::ExprData::Field { expr, field } => ExprData::Field {
                expr: mdl.lower_expr(*expr),
                field: match field {
                    crate::types::Field::AdtField(adt_field) => Field::AdtField(
                        mdl.lower_adt(adt_field.adt()),
                        AdtField::new(db, adt_field.name(db), mdl.lower_ty(adt_field.ty())),
                    ),
                    crate::types::Field::List(ty, f) => Field::List(mdl.lower_ty(*ty), *f),
                    crate::types::Field::Undefined => Field::Undefined,
                },
            },
            hir::ExprData::Adt { adt, fields } => ExprData::Adt {
                adt: mdl.lower_adt(*adt),
                fields: fields
                    .iter()
                    .map(|f| {
                        (
                            AdtField::new(db, f.decl.name(db), mdl.lower_ty(f.decl.ty())),
                            mdl.lower_expr(f.value),
                        )
                    })
                    .collect(),
            },
            hir::ExprData::Missing => ExprData::Missing,
            hir::ExprData::If(it) => ExprData::If(IfExpr {
                condition: mdl.lower_expr(it.condition),
                then_branch: mdl.lower_expr(it.then_branch),
                else_branch: it.else_branch.map(|expr| mdl.lower_expr(expr)),
            }),
            hir::ExprData::While(it) => ExprData::While(WhileExpr {
                expr: mdl.lower_expr(it.expr),
                invariants: it
                    .invariants
                    .iter()
                    .map(|invs| invs.iter().map(|expr| mdl.lower_expr(*expr)).collect())
                    .collect(),
                decreases: match it.decreases {
                    hir::Decreases::Unspecified => Decreases::Unspecified,
                    hir::Decreases::Expr(expr) => Decreases::Expr(mdl.lower_expr(expr)),
                    hir::Decreases::Inferred => Decreases::Inferred,
                },
                body: mdl.lower_expr(it.body),
            }),
            hir::ExprData::For(it) => ExprData::For(ForExpr {
                is_ghost: it.is_ghost,
                variable: mdl.lower_var(it.variable),
                in_expr: mdl.lower_expr(it.in_expr),
                invariants: it
                    .invariants
                    .iter()
                    .map(|invs| invs.iter().map(|expr| mdl.lower_expr(*expr)).collect())
                    .collect(),
                body: mdl.lower_expr(it.body),
            }),
            hir::ExprData::Call { expr, args } => ExprData::Call {
                expr: mdl.lower_expr(*expr),
                args: args.iter().map(|expr| mdl.lower_expr(*expr)).collect(),
            },
            &hir::ExprData::Unary { op, inner } => {
                ExprData::Unary { op, inner: mdl.lower_expr(inner) }
            }
            &hir::ExprData::Bin { lhs, op, rhs } => {
                ExprData::Bin { lhs: mdl.lower_expr(lhs), op, rhs: mdl.lower_expr(rhs) }
            }
            &hir::ExprData::Ref { is_mut, expr } => {
                ExprData::Ref { is_mut, expr: mdl.lower_expr(expr) }
            }
            &hir::ExprData::Index { base, index } => {
                ExprData::Index { base: mdl.lower_expr(base), index: mdl.lower_expr(index) }
            }
            hir::ExprData::List { elems } => {
                ExprData::List { elems: elems.iter().map(|&id| mdl.lower_expr(id)).collect() }
            }
            hir::ExprData::Quantifier { quantifier, over, expr } => ExprData::Quantifier {
                quantifier: *quantifier,
                over: match over {
                    hir::QuantifierOver::Vars(vars) => {
                        QuantifierOver::Vars(vars.iter().map(|var| mdl.lower_var(*var)).collect())
                    }
                    hir::QuantifierOver::In(var, expr) => {
                        QuantifierOver::In(mdl.lower_var(*var), mdl.lower_expr(*expr))
                    }
                },
                expr: mdl.lower_expr(*expr),
            },
            hir::ExprData::Result => ExprData::Result,
            hir::ExprData::Range { lhs, rhs } => ExprData::Range {
                lhs: lhs.map(|it| mdl.lower_expr(it)),
                rhs: rhs.map(|it| mdl.lower_expr(it)),
            },
            hir::ExprData::Return(it) => ExprData::Return(it.map(|it| mdl.lower_expr(it))),
            hir::ExprData::NotNull(it) => ExprData::NotNull(mdl.lower_expr(*it)),
            hir::ExprData::Builtin(it) => ExprData::Builtin(match it {
                hir::BuiltinExpr::RangeMin(it) => BuiltinExpr::RangeMin(mdl.lower_expr(*it)),
                hir::BuiltinExpr::RangeMax(it) => BuiltinExpr::RangeMax(mdl.lower_expr(*it)),
                hir::BuiltinExpr::InRange(lhs, rhs) => {
                    BuiltinExpr::InRange(mdl.lower_expr(*lhs), mdl.lower_expr(*rhs))
                }
            }),
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
}

impl Field {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        match self {
            Field::Undefined => Name::new("<undefined field>"),
            Field::AdtField(_, f) => f.name(db),
            Field::List(_, l) => match l {
                ListField::Len => Name::new("len"),
            },
        }
    }
}
