use std::{ops::ControlFlow, sync::Arc};

use derive_new::new;

use crate::hir::{
    self, Block, Decreases, ExprData, ExprIdx, Field, Function, Ident, IfExpr, ItemContext,
    ItemSourceMap, Param, Program, Statement, StatementData, TypeData, TypeDecl, TypeInvariant,
    TypeSrcId, VariableIdx, VariableRef,
};

pub trait Walker<'db>: Sized {
    fn init(db: &'db dyn crate::Db, vcx: VisitContext) -> Self
    where
        Self:;
    fn walk_program<'v, V: Visitor>(
        db: &'db dyn crate::Db,
        program: Program,
        visitor: &'v mut V,
    ) -> ControlFlow<V::Item> {
        for &item_id in program.items(db) {
            let Some(item) = hir::item(db, program, item_id) else { continue };
            let Some((cx, source_map)) = hir::item_lower(db, program, item_id, item) else { continue };
            let cx = Arc::new(cx);
            let source_map = Arc::new(source_map);
            let mut walker = Self::init(db, VisitContext { cx, source_map });
            match item {
                hir::Item::Type(ty_decl) => {
                    walker.walk_ty_decl(visitor, program, ty_decl)?;
                }
                hir::Item::TypeInvariant(ty_inv) => {
                    walker.walk_ty_inv(visitor, program, ty_inv)?;
                }
                hir::Item::Function(f) => {
                    walker.walk_function(visitor, f)?;
                }
            }
        }
        ControlFlow::Continue(())
    }
    fn walk_ty_decl<V: Visitor>(
        &mut self,
        visitor: &mut V,
        program: Program,
        ty_decl: TypeDecl,
    ) -> ControlFlow<V::Item>;
    fn walk_ty_inv<V: Visitor>(
        &mut self,
        visitor: &mut V,
        program: Program,
        ty_inv: TypeInvariant,
    ) -> ControlFlow<V::Item>;
    fn walk_field<V: Visitor>(
        &mut self,
        visitor: &mut V,
        field: &Field,
        reference: &Ident,
    ) -> ControlFlow<V::Item>;
    fn walk_function<V: Visitor>(
        &mut self,
        visitor: &mut V,
        function: Function,
    ) -> ControlFlow<V::Item>;
    fn walk_ty<V: Visitor>(&mut self, visitor: &mut V, ty: TypeSrcId) -> ControlFlow<V::Item>;
    fn walk_decreases<V: Visitor>(
        &mut self,
        visitor: &mut V,
        decreases: Decreases,
    ) -> ControlFlow<V::Item>;
    fn walk_exprs<V: Visitor>(
        &mut self,
        visitor: &mut V,
        exprs: &[ExprIdx],
    ) -> ControlFlow<V::Item>;
    fn walk_expr<V: Visitor>(&mut self, visitor: &mut V, expr: ExprIdx) -> ControlFlow<V::Item>;
    fn walk_if_expr<V: Visitor>(
        &mut self,
        visitor: &mut V,
        if_expr: &IfExpr,
    ) -> ControlFlow<V::Item>;
    fn walk_block<V: Visitor>(&mut self, visitor: &mut V, block: &Block) -> ControlFlow<V::Item>;
    fn walk_param_list<V: Visitor>(
        &mut self,
        visitor: &mut V,
        param_list: &[Param<VariableIdx>],
    ) -> ControlFlow<V::Item>;
}

pub struct VisitContext {
    pub cx: Arc<ItemContext>,
    pub source_map: Arc<ItemSourceMap>,
}

#[allow(unused)]
pub trait Visitor {
    type Item;

    #[must_use]
    fn visit_ty_decl(&mut self, vcx: &VisitContext, ty_decl: TypeDecl) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_function(
        &mut self,
        vcx: &VisitContext,
        function: Function,
    ) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_field(
        &mut self,
        vcx: &VisitContext,
        field: &Field,
        reference: &Ident,
    ) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_var(&mut self, vcx: &VisitContext, var: VariableRef) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_param(
        &mut self,
        vcx: &VisitContext,
        param: &Param<VariableIdx, TypeSrcId>,
    ) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_expr(&mut self, vcx: &VisitContext, expr: ExprIdx) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_decreases(
        &mut self,
        vcx: &VisitContext,
        decreases: Decreases,
    ) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_ty(&mut self, vcx: &VisitContext, ty: TypeSrcId) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_stmt(&mut self, vcx: &VisitContext, stmt: &Statement) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
}

#[derive(new)]
pub struct OrderedWalk<'db, O> {
    db: &'db dyn crate::Db,
    vcx: VisitContext,
    order: O,
}

pub trait Order {
    fn visit_pre(&self) -> bool;
    fn visit_post(&self) -> bool;
}

#[derive(Default)]
pub struct PreOrder;
impl Order for PreOrder {
    fn visit_pre(&self) -> bool {
        true
    }
    fn visit_post(&self) -> bool {
        false
    }
}
pub type PreOrderWalk<'a> = OrderedWalk<'a, PreOrder>;

#[derive(Default)]
pub struct PostOrder;
impl Order for PostOrder {
    fn visit_pre(&self) -> bool {
        false
    }
    fn visit_post(&self) -> bool {
        true
    }
}
pub type PostOrderWalk<'a> = OrderedWalk<'a, PostOrder>;

impl<O> OrderedWalk<'_, O>
where
    O: Order,
{
    fn pre(&mut self) -> bool {
        self.order.visit_pre()
    }
    fn post(&mut self) -> bool {
        self.order.visit_post()
    }
}

impl<'db, O> Walker<'db> for OrderedWalk<'db, O>
where
    O: Order + Default,
{
    fn init(db: &'db dyn crate::Db, vcx: VisitContext) -> Self {
        Self {
            db,
            vcx,
            order: O::default(),
        }
    }

    fn walk_ty_decl<V: Visitor>(
        &mut self,
        visitor: &mut V,
        program: Program,
        ty_decl: TypeDecl,
    ) -> ControlFlow<V::Item> {
        if self.pre() {
            visitor.visit_ty_decl(&self.vcx, ty_decl)?;
        }
        match ty_decl.data(self.db) {
            hir::TypeDeclData::Struct(s) => {
                // TODO: Walk the name of the struct
                // self.walk_ty(
                //     visitor,
                //     hir::find_named_type(self.db, program, s.name(self.db)),
                // )?;
                for f in hir::struct_fields(self.db, s) {
                    self.walk_field(visitor, &f, &f.name)?
                }
            }
        }
        if self.post() {
            visitor.visit_ty_decl(&self.vcx, ty_decl)?;
        }
        ControlFlow::Continue(())
    }

    fn walk_ty_inv<V: Visitor>(
        &mut self,
        visitor: &mut V,
        program: Program,
        ty_inv: TypeInvariant,
    ) -> ControlFlow<V::Item> {
        // TODO: Walk the name of the struct
        // self.walk_ty(
        //     visitor,
        //     hir::find_named_type(self.db, program, ty_inv.name(self.db)),
        // )?;
        if let Some(body_expr) = self.vcx.cx.body_expr() {
            self.walk_expr(visitor, body_expr)?;
        }
        ControlFlow::Continue(())
    }

    fn walk_field<V: Visitor>(
        &mut self,
        visitor: &mut V,
        field: &Field,
        reference: &Ident,
    ) -> ControlFlow<V::Item> {
        if self.pre() {
            visitor.visit_field(&self.vcx, field, reference)?;
        }
        // TODO: Walk the actual type
        // self.walk_ty(visitor, field.ty);
        if self.post() {
            visitor.visit_field(&self.vcx, field, reference)?;
        }
        ControlFlow::Continue(())
    }

    fn walk_function<V: Visitor>(
        &mut self,
        visitor: &mut V,
        function: Function,
    ) -> ControlFlow<V::Item> {
        let Some(fx) = self.vcx.cx.function_context().cloned() else { return ControlFlow::Continue(()) };

        visitor.visit_var(&self.vcx, fx.function_var())?;

        let params = self.vcx.cx.params().to_vec();
        self.walk_param_list(visitor, &params)?;

        for it in fx.conditions() {
            self.walk_exprs(visitor, it.exprs())?;
        }

        self.walk_decreases(visitor, fx.decreases())?;

        if let Some(ret_ty) = fx.return_ty_src() {
            self.walk_ty(visitor, ret_ty)?;
        }

        if let Some(body_expr) = self.vcx.cx.body_expr() {
            self.walk_expr(visitor, body_expr)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_ty<V: Visitor>(&mut self, visitor: &mut V, ty: TypeSrcId) -> ControlFlow<V::Item> {
        if self.pre() {
            visitor.visit_ty(&self.vcx, ty)?;
        }

        let td = if let Some(td) = &self.vcx.cx[ty].data {
            td.clone()
        } else {
            return ControlFlow::Continue(());
        };

        match td {
            TypeData::Error
            | TypeData::Void
            | TypeData::Primitive(_)
            | TypeData::Null
            | TypeData::Free => {}
            TypeData::Ghost(inner)
            | TypeData::Ref { inner, .. }
            | TypeData::List(inner)
            | TypeData::Range(inner)
            | TypeData::Optional(inner) => {
                self.walk_ty(visitor, inner)?;
            }
            TypeData::Struct(_) => {}
            TypeData::Function {
                params, return_ty, ..
            } => {
                for param in params.iter() {
                    self.walk_ty(visitor, param.ty)?;
                }
                self.walk_ty(visitor, return_ty)?;
            }
        }
        if self.post() {
            visitor.visit_ty(&self.vcx, ty)?;
        }
        ControlFlow::Continue(())
    }

    fn walk_decreases<V: Visitor>(
        &mut self,
        visitor: &mut V,
        decreases: Decreases,
    ) -> ControlFlow<V::Item> {
        if self.pre() {
            visitor.visit_decreases(&self.vcx, decreases)?;
        }
        match decreases {
            Decreases::Expr(expr) => self.walk_expr(visitor, expr)?,
            Decreases::Unspecified | Decreases::Inferred => {}
        }
        if self.post() {
            visitor.visit_decreases(&self.vcx, decreases)?;
        }
        ControlFlow::Continue(())
    }

    fn walk_exprs<V: Visitor>(
        &mut self,
        visitor: &mut V,
        exprs: &[ExprIdx],
    ) -> ControlFlow<V::Item> {
        for expr in exprs {
            self.walk_expr(visitor, *expr)?;
        }
        ControlFlow::Continue(())
    }
    fn walk_expr<V: Visitor>(&mut self, visitor: &mut V, expr: ExprIdx) -> ControlFlow<V::Item> {
        if self.pre() {
            visitor.visit_expr(&self.vcx, expr)?;
        }

        match self.vcx.cx.expr(expr).data.clone() {
            ExprData::Literal(_) | ExprData::Missing | ExprData::Result => {}
            ExprData::Ident(var) => {
                visitor.visit_var(&self.vcx, var)?;
            }
            ExprData::Field {
                expr,
                field,
                field_name,
                ..
            } => {
                self.walk_expr(visitor, expr)?;
                if let Some(field) = field {
                    self.walk_field(visitor, &field, &field_name)?;
                }
            }
            ExprData::Struct { fields, .. } => {
                for f in fields {
                    self.walk_field(visitor, &f.decl, &f.name)?;
                    self.walk_expr(visitor, f.value)?;
                }
            }
            ExprData::If(if_expr) => {
                self.walk_if_expr(visitor, &if_expr)?;
            }
            ExprData::Call { expr, args } => {
                self.walk_expr(visitor, expr)?;
                for arg in args {
                    self.walk_expr(visitor, arg)?;
                }
            }
            ExprData::Block(block) => {
                self.walk_block(visitor, &block)?;
            }
            ExprData::Return(Some(inner)) => {
                self.walk_expr(visitor, inner)?;
            }
            ExprData::Return(None) => {}
            ExprData::Bin { lhs, op: _, rhs } => {
                self.walk_expr(visitor, lhs)?;
                self.walk_expr(visitor, rhs)?;
            }
            ExprData::Unary { op: _, inner } => {
                self.walk_expr(visitor, inner)?;
            }
            ExprData::Ref { expr, .. } => {
                self.walk_expr(visitor, expr)?;
            }
            ExprData::Index { base, index } => {
                self.walk_expr(visitor, base)?;
                self.walk_expr(visitor, index)?;
            }
            ExprData::Range { lhs, rhs } => {
                if let Some(e) = lhs {
                    self.walk_expr(visitor, e)?;
                }
                if let Some(e) = rhs {
                    self.walk_expr(visitor, e)?;
                }
            }
            ExprData::List { elems } => {
                for elem in elems {
                    self.walk_expr(visitor, elem)?;
                }
            }
            ExprData::Quantifier { params, expr, .. } => {
                self.walk_param_list(visitor, &params)?;
                self.walk_expr(visitor, expr)?;
            }
        };

        if self.post() {
            visitor.visit_expr(&self.vcx, expr)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_if_expr<V: Visitor>(
        &mut self,
        visitor: &mut V,
        if_expr: &IfExpr,
    ) -> ControlFlow<V::Item> {
        self.walk_expr(visitor, if_expr.condition)?;
        self.walk_expr(visitor, if_expr.then_branch)?;
        match if_expr.else_branch {
            Some(e) => self.walk_expr(visitor, e),
            None => ControlFlow::Continue(()),
        }
    }

    fn walk_block<V: Visitor>(&mut self, visitor: &mut V, block: &Block) -> ControlFlow<V::Item> {
        for stmt in &block.stmts {
            if self.pre() {
                visitor.visit_stmt(&self.vcx, stmt)?;
            }

            match &stmt.data {
                StatementData::Expr(expr) => self.walk_expr(visitor, *expr)?,
                &StatementData::Let {
                    variable,
                    explicit_ty,
                    initializer,
                } => {
                    visitor.visit_var(&self.vcx, variable)?;
                    if let Some(ty) = explicit_ty {
                        self.walk_ty(visitor, ty)?;
                    }
                    self.walk_expr(visitor, initializer)?;
                }
                StatementData::While {
                    expr,
                    invariants,
                    decreases,
                    body,
                } => {
                    self.walk_expr(visitor, *expr)?;
                    for inv in invariants {
                        self.walk_exprs(visitor, inv)?;
                    }
                    self.walk_decreases(visitor, *decreases)?;
                    self.walk_block(visitor, body)?;
                }
                StatementData::Assertion { exprs, .. } => self.walk_exprs(visitor, exprs)?,
            }

            if self.post() {
                visitor.visit_stmt(&self.vcx, stmt)?;
            }
        }

        if let Some(expr) = block.tail_expr {
            self.walk_expr(visitor, expr)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_param_list<V: Visitor>(
        &mut self,
        visitor: &mut V,
        param_list: &[Param<VariableIdx>],
    ) -> ControlFlow<V::Item> {
        for param in param_list {
            if self.pre() {
                visitor.visit_param(&self.vcx, param)?;
            }
            self.walk_ty(visitor, param.ty)?;
            if self.post() {
                visitor.visit_param(&self.vcx, param)?;
            }
        }

        ControlFlow::Continue(())
    }
}
