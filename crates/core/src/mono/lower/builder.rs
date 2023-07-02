use crate::{
    def::Def,
    hir::Literal,
    mono::{
        exprs::{
            Block, Decreases, ExprData, ExprDataWrapper, ExprPtr, Field, Statement, StatementData,
            StatementDataWrapper, VariablePtr, WhileExpr,
        },
        types::Type,
    },
};

pub struct Builder<'db> {
    pub db: &'db dyn crate::Db,
}

impl<'db> Builder<'db> {
    pub fn alloc(&self, src: ExprPtr, ty: Type, data: ExprData) -> ExprPtr {
        ExprPtr { def: src.def, id: src.id, ty, inner_data: ExprDataWrapper::new(self.db, data) }
    }

    pub fn block(
        &self,
        src: ExprPtr,
        stmts: Vec<Statement>,
        tail_expr: Option<ExprPtr>,
    ) -> ExprPtr {
        let ty = tail_expr.map(|e| e.ty()).unwrap_or_else(|| Type::void(self.db));
        self.alloc(src, ty, ExprData::Block(Block { stmts, tail_expr }))
    }
    pub fn while_expr(
        &self,
        src: ExprPtr,
        expr: ExprPtr,
        invariants: Vec<Vec<ExprPtr>>,
        decreases: Decreases,
        body: ExprPtr,
    ) -> ExprPtr {
        self.alloc(
            src,
            Type::void(self.db),
            ExprData::While(WhileExpr { expr, invariants, decreases, body }),
        )
    }

    pub fn stmt(&self, def: Def, data: StatementData) -> Statement {
        Statement { def, inner_data: StatementDataWrapper::new(self.db, data) }
    }
    pub fn lit(&self, src: ExprPtr, lit: impl Into<Literal>) -> ExprPtr {
        let lit: Literal = lit.into();
        let ty = match lit {
            Literal::Null => Type::null(self.db),
            Literal::Int(_) => Type::int(self.db),
            Literal::Bool(_) => Type::bool(self.db),
        };
        self.alloc(src, ty, ExprData::Literal(lit))
    }

    pub fn var_expr(&self, src: ExprPtr, var: VariablePtr) -> ExprPtr {
        self.alloc(src, var.ty(), ExprData::Ident(var))
    }

    pub fn expr_stmt(&self, expr: ExprPtr) -> Statement {
        Statement {
            def: expr.def,
            inner_data: StatementDataWrapper::new(self.db, StatementData::Expr(expr)),
        }
    }

    pub fn field(&self, src: ExprPtr, expr: ExprPtr, field: Field) -> ExprPtr {
        self.alloc(src, field.ty(self.db), ExprData::Field { expr, field })
    }

    pub(crate) fn quantifier(
        &self,
        src: ExprPtr,
        quantifier: crate::hir::Quantifier,
        over: crate::mono::exprs::QuantifierOver,
        expr: ExprPtr,
    ) -> ExprPtr {
        self.alloc(src, Type::bool(self.db), ExprData::Quantifier { quantifier, over, expr })
    }
}

#[doc(hidden = true)]
pub mod prelude {
    pub use mist_syntax::ast::operators::{ArithOp, BinaryOp, CmpOp, LogicOp, UnaryOp};

    pub use crate::mono::exprs::{IfExpr, Let, StatementData};
}

#[doc(hidden = true)]
#[macro_export]
macro_rules! binary_op_ {
    ($b:expr,$src:expr,$l:tt, $r:tt, $ty:expr, $op:expr) => {{
        use $crate::mono::lower::builder::prelude::*;
        let lhs = build!($b, $src, $l);
        let rhs = build!($b, $src, $r);
        $b.alloc($src, Type::int($b.db), ExprData::Bin { lhs, op: $op, rhs })
    }};
}
pub use binary_op_ as binary_op;

#[macro_export]
macro_rules! build_ {
    ($b:expr, $src:expr, $e:literal) => {
        $b.lit($src, $e)
    };
    ($b:expr, $src:expr, $e:ident) => {
        $e
    };
    ($b:expr, $src:expr, $l:tt + $r:tt) => {
        $crate::mono::lower::builder::binary_op!($b, $src, $l, $r, Type::int($b.db), BinaryOp::ArithOp(ArithOp::Add))
    };
    ($b:expr, $src:expr, $l:tt = $r:tt) => {
        $crate::mono::lower::builder::binary_op!($b, $src, $l, $r, Type::int($b.db), BinaryOp::Assignment)
    };
    ($b:expr, $src:expr, $l:tt || $r:tt) => {
        $crate::mono::lower::builder::binary_op!($b, $src, $l, $r, Type::bool($b.db), BinaryOp::LogicOp(LogicOp::Or))
    };
    ($b:expr, $src:expr, $l:tt < $r:tt) => {
        $crate::mono::lower::builder::binary_op!($b, $src, $l, $r, Type::bool($b.db), BinaryOp::lt())
    };
    ($b:expr, $src:expr, $l:tt <= $r:tt) => {
        $crate::mono::lower::builder::binary_op!($b, $src, $l, $r, Type::bool($b.db), BinaryOp::le())
    };
    ($b:expr, $src:expr, $l:tt > $r:tt) => {
        $crate::mono::lower::builder::binary_op!($b, $src, $l, $r, Type::bool($b.db), BinaryOp::gt())
    };
    ($b:expr, $src:expr, $l:tt >= $r:tt) => {
        $crate::mono::lower::builder::binary_op!($b, $src, $l, $r, Type::bool($b.db), BinaryOp::ge())
    };
    ($b:expr, $src:expr, if $cond:tt { $then:tt }) => {{
        use $crate::mono::lower::builder::prelude::*;
        let if_expr = ExprData::If(IfExpr { condition: $cond, then_branch: $then, else_branch: None });
        $b.alloc($src, Type::bool($b.db), if_expr)
    }};
    ($b:expr, $src:expr, if $cond:tt { $then:tt } else { $else:tt }) => {{
        use $crate::mono::lower::builder::prelude::*;
        let if_expr = ExprData::If(IfExpr { condition: $cond, then_branch: $then, else_branch: Some($else) });
        $b.alloc($src, Type::bool($b.db), if_expr)
    }};
    ($b:expr, $src:expr, let $var:tt = $val:tt) => {{
        use $crate::mono::lower::builder::prelude::*;
        $b.stmt($src.def, StatementData::Let(Let { variable: Some($var), initializer: $val }))
    }};
    ($b:expr, $src:expr, { $($tt:tt)* }) => {
        build!($b, $src, $($tt)*)
    };
}
pub use build_ as build;
