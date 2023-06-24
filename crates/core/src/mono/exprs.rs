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
            Field::Builtin(bf) => bf.name(),
        }
    }
    pub fn from_adt_field(db: &dyn crate::Db, adt_field: AdtField) -> Field {
        Field::AdtField(adt_field.adt(db), adt_field)
    }
}
