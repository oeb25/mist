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
}
