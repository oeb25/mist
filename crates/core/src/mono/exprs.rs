use std::fmt;

use itertools::{Either, Itertools};
use mist_syntax::ast::{
    self,
    operators::{BinaryOp, UnaryOp},
};

use crate::{
    def::{Def, Name},
    hir::{AssertionKind, ExprIdx, Literal, Quantifier, SpanOrAstPtr, VariableIdx},
    types::BuiltinField,
};

use super::{
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
pub struct Statement {
    pub(super) def: Def,
    pub(super) inner_data: StatementDataWrapper,
}
#[salsa::interned]
pub struct StatementDataWrapper {
    data: StatementData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StatementData {
    Expr(ExprPtr),
    Let(Let),
    Assertion { kind: AssertionKind, exprs: Vec<ExprPtr> },
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
    Builtin(BuiltinField<Type>, Type),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum QuantifierOver {
    Vars(Vec<VariablePtr>),
    In(Vec<(VariablePtr, ExprPtr)>),
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BuiltinExpr {
    RangeMin(ExprPtr),
    RangeMax(ExprPtr),
    InRange(ExprPtr, ExprPtr),
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    pub stmts: Vec<Statement>,
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
    pub fn visit(self, db: &dyn crate::Db, f: &mut impl FnMut(Either<ExprPtr, Statement>)) {
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
                    QuantifierOver::In(vars) => {
                        for (_, e) in vars {
                            e.visit(db, f)
                        }
                    }
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
    pub fn display(self, db: &dyn crate::Db) -> impl fmt::Display {
        match self.data(db) {
            ExprData::Literal(l) => l.to_string(),
            ExprData::Self_ => "self".to_string(),
            ExprData::Ident(var) => var.name(db).to_string(),
            ExprData::Field { expr, field } => {
                format!("{}.{}", expr.display(db), field.name(db))
            }
            ExprData::Adt { adt, fields } => {
                let fields = fields
                    .iter()
                    .map(|(f, v)| format!("{}: {}", f.name(db), v.display(db)))
                    .format(", ");
                format!("{} {{ {fields} }}", adt.display(db))
            }
            ExprData::Missing => todo!(),
            ExprData::Block(b) => {
                if b.stmts.is_empty() && b.tail_expr.is_none() {
                    "{}".to_string()
                } else {
                    format!(
                        "{{\n{}\n}}",
                        b.stmts
                            .iter()
                            .map(|s| s.display(db).to_string())
                            .chain(b.tail_expr.map(|e| e.display(db).to_string()))
                            .join("\n")
                            .lines()
                            .map(|l| format!("  {l}"))
                            .format("\n")
                    )
                }
            }
            ExprData::If(it) => format!(
                "if {} {}{}",
                it.condition.display(db),
                it.then_branch.display(db),
                if let Some(e) = it.else_branch {
                    format!(" else {}", e.display(db))
                } else {
                    String::new()
                }
            ),
            ExprData::While(w) => {
                let cond_and_stuff =
                    [w.expr.display(db).to_string()]
                        .into_iter()
                        .chain(w.invariants.iter().flat_map(|invs| {
                            invs.iter().map(|inv| format!("inv {}", inv.display(db)))
                        }))
                        .format("\n  ");
                let body = w.body.display(db);
                format!("while {cond_and_stuff}\n{body}")
            }
            ExprData::For(_) => todo!(),
            ExprData::Call { fun, args } => {
                let fun = fun.display(db);
                let args = args.iter().map(|arg| arg.display(db)).format(", ");
                format!("{fun}({args})")
            }
            ExprData::Unary { op, inner } => format!("{op}{}", inner.display(db)),
            ExprData::Bin { lhs, op, rhs } => {
                format!("{} {op} {}", lhs.display(db), rhs.display(db))
            }
            ExprData::Ref { is_mut, expr } => {
                if is_mut {
                    format!("&mut {}", expr.display(db))
                } else {
                    format!("&{}", expr.display(db))
                }
            }
            ExprData::Index { base, index } => {
                format!("{}[{}]", base.display(db), index.display(db))
            }
            ExprData::List { elems } => {
                format!("[{}]", elems.iter().map(|e| e.display(db)).format(", "))
            }
            ExprData::Quantifier { quantifier, over, expr } => match over {
                QuantifierOver::Vars(vars) => {
                    format!(
                        "{quantifier}({}) {{ {} }}",
                        vars.iter()
                            .map(|var| format!("{}: {}", var.name(db), var.ty().display(db)))
                            .format(", "),
                        expr.display(db)
                    )
                }
                QuantifierOver::In(vars) => {
                    let vars = vars
                        .iter()
                        .map(|(var, in_expr)| {
                            format!("{} in {}", var.name(db), in_expr.display(db),)
                        })
                        .format(", ");

                    format!("{quantifier} {vars} {{ {} }}", expr.display(db))
                }
            },
            ExprData::Result => todo!(),
            ExprData::Range { lhs, rhs } => {
                format!(
                    "({}..{})",
                    lhs.map(|lhs| lhs.display(db).to_string()).unwrap_or_default(),
                    rhs.map(|rhs| rhs.display(db).to_string()).unwrap_or_default()
                )
            }
            ExprData::Return(_) => todo!(),
            ExprData::NotNull(_) => todo!(),
            ExprData::Builtin(bi) => match bi {
                BuiltinExpr::RangeMin(e) => format!("{}.min", e.display(db)),
                BuiltinExpr::RangeMax(e) => format!("{}.max", e.display(db)),
                BuiltinExpr::InRange(i, r) => format!("{} in {}", i.display(db), r.display(db)),
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

impl Statement {
    pub fn def(&self) -> Def {
        self.def
    }
    pub fn data(&self, db: &dyn crate::Db) -> StatementData {
        self.inner_data.data(db)
    }
    pub fn visit(self, db: &dyn crate::Db, f: &mut impl FnMut(Either<ExprPtr, Statement>)) {
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
    pub fn display(self, db: &dyn crate::Db) -> impl fmt::Display {
        match self.data(db) {
            StatementData::Expr(e) => format!("{};", e.display(db)),
            StatementData::Let(l) => format!(
                "let {}: {} = {};",
                l.variable.map(|var| var.name(db).to_string()).unwrap_or_else(|| "??".to_string()),
                l.initializer.ty().display(db),
                l.initializer.display(db),
            ),
            StatementData::Assertion { kind, exprs } => {
                format!("{kind} {};", exprs.iter().map(|e| e.display(db)).format(", "))
            }
        }
    }
}

impl Field {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        match self {
            Field::Undefined => Name::new("<undefined field>"),
            Field::AdtField(_, f) => f.name(db),
            Field::Builtin(bf, _) => bf.name(),
        }
    }
    pub fn from_adt_field(db: &dyn crate::Db, adt_field: AdtField) -> Field {
        Field::AdtField(adt_field.adt(db), adt_field)
    }
    pub fn ty(self, db: &dyn crate::Db) -> Type {
        match self {
            Field::Undefined => Type::error(db),
            Field::AdtField(_, f) => f.ty(db),
            Field::Builtin(_, ty) => ty,
        }
    }
}

impl ExprFunction {
    fn display(&self, db: &dyn crate::Db) -> impl fmt::Display {
        match self {
            ExprFunction::Expr(e) => e.display(db).to_string(),
            ExprFunction::Builtin(b) => b.name().to_string(),
        }
    }
}
