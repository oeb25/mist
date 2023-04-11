use std::ops::ControlFlow;

use derive_new::new;

use crate::{
    ir::{
        self, Block, Decreases, Else, ExprData, ExprIdx, Field, Function, Ident, IfExpr, Param,
        ParamList, Program, Statement, StatementData, Type, TypeData, TypeDecl, TypeInvariant,
        VariableRef,
    },
    typecheck::ItemContext,
};

pub trait Walker {
    fn walk_program<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        program: Program,
    ) -> ControlFlow<T>;
    fn walk_ty_decl<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        program: Program,
        cx: &ItemContext,
        ty_decl: TypeDecl,
    ) -> ControlFlow<T>;
    fn walk_ty_inv<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        program: Program,
        cx: &ItemContext,
        ty_inv: TypeInvariant,
    ) -> ControlFlow<T>;
    fn walk_field<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        field: &Field,
        reference: &Ident,
    ) -> ControlFlow<T>;
    fn walk_function<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        program: Program,
        cx: &ItemContext,
        function: Function,
    ) -> ControlFlow<T>;
    fn walk_ty<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        ty: Type,
    ) -> ControlFlow<T>;
    fn walk_decreases<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        decreases: Decreases,
    ) -> ControlFlow<T>;
    fn walk_exprs<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        exprs: &[ExprIdx],
    ) -> ControlFlow<T>;
    fn walk_expr<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        expr: ExprIdx,
    ) -> ControlFlow<T>;
    fn walk_if_expr<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        if_expr: &IfExpr,
    ) -> ControlFlow<T>;
    fn walk_block<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        block: &Block,
    ) -> ControlFlow<T>;
    fn walk_param_list<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        param_list: &ParamList,
    ) -> ControlFlow<T>;

    fn ty<T>(&mut self, visitor: &mut impl Visitor<T>, cx: &ItemContext, ty: Type) -> Option<T> {
        self.walk_ty(visitor, cx, ty).break_value()
    }
    fn exprs<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        exprs: &[ExprIdx],
    ) -> Option<T> {
        self.walk_exprs(visitor, cx, exprs).break_value()
    }
    fn expr<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        expr: ExprIdx,
    ) -> Option<T> {
        self.walk_expr(visitor, cx, expr).break_value()
    }
    fn if_expr<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        if_expr: &IfExpr,
    ) -> Option<T> {
        self.walk_if_expr(visitor, cx, if_expr).break_value()
    }
    fn block<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        block: &Block,
    ) -> Option<T> {
        self.walk_block(visitor, cx, block).break_value()
    }
    fn param_list<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        param_list: &ParamList,
    ) -> Option<T> {
        self.walk_param_list(visitor, cx, param_list).break_value()
    }
}

#[allow(unused)]
pub trait Visitor<T> {
    #[must_use]
    fn visit_ty_decl(&mut self, cx: &ItemContext, ty_decl: TypeDecl) -> ControlFlow<T> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_function(&mut self, cx: &ItemContext, function: Function) -> ControlFlow<T> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_field(
        &mut self,
        cx: &ItemContext,
        field: &Field,
        reference: &Ident,
    ) -> ControlFlow<T> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_var(&mut self, cx: &ItemContext, var: VariableRef) -> ControlFlow<T> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_param(&mut self, cx: &ItemContext, param: &Param) -> ControlFlow<T> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_expr(&mut self, cx: &ItemContext, expr: ExprIdx) -> ControlFlow<T> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_decreases(&mut self, cx: &ItemContext, decreases: Decreases) -> ControlFlow<T> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_ty(&mut self, cx: &ItemContext, ty: Type) -> ControlFlow<T> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_stmt(&mut self, cx: &ItemContext, stmt: &Statement) -> ControlFlow<T> {
        ControlFlow::Continue(())
    }
}

#[derive(new)]
pub struct OrderedWalk<'a, O> {
    db: &'a dyn crate::Db,
    order: O,
}

pub trait Order {
    fn visit_pre(&self) -> bool;
    fn visit_post(&self) -> bool;
}

pub struct PreOrder;
impl PreOrder {
    pub fn new(db: &dyn crate::Db) -> OrderedWalk<PreOrder> {
        OrderedWalk { db, order: Self }
    }
}
impl Order for PreOrder {
    fn visit_pre(&self) -> bool {
        true
    }
    fn visit_post(&self) -> bool {
        false
    }
}

pub struct PostOrder;
impl PostOrder {
    pub fn new(db: &dyn crate::Db) -> OrderedWalk<PostOrder> {
        OrderedWalk { db, order: Self }
    }
}
impl Order for PostOrder {
    fn visit_pre(&self) -> bool {
        false
    }
    fn visit_post(&self) -> bool {
        true
    }
}

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

impl<O> Walker for OrderedWalk<'_, O>
where
    O: Order,
{
    fn walk_program<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        program: Program,
    ) -> ControlFlow<T> {
        walk_program(self, self.db, visitor, program)
    }

    fn walk_ty_decl<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        program: Program,
        cx: &ItemContext,
        ty_decl: TypeDecl,
    ) -> ControlFlow<T> {
        if self.pre() {
            visitor.visit_ty_decl(cx, ty_decl)?;
        }
        match ty_decl.data(self.db) {
            ir::TypeDeclData::Struct(s) => {
                self.walk_ty(
                    visitor,
                    cx,
                    ir::find_named_type(self.db, program, s.name(self.db)),
                )?;
                for f in ir::struct_fields(self.db, program, s) {
                    self.walk_field(visitor, cx, &f, &f.name)?
                }
            }
        }
        if self.post() {
            visitor.visit_ty_decl(cx, ty_decl)?;
        }
        ControlFlow::Continue(())
    }

    fn walk_ty_inv<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        program: Program,
        cx: &ItemContext,
        ty_inv: TypeInvariant,
    ) -> ControlFlow<T> {
        self.walk_ty(
            visitor,
            cx,
            ir::find_named_type(self.db, program, ty_inv.name(self.db)),
        )?;
        self.walk_block(visitor, cx, &ir::ty_inv_block(self.db, program, ty_inv).1)
    }

    fn walk_field<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        field: &Field,
        reference: &Ident,
    ) -> ControlFlow<T> {
        if self.pre() {
            visitor.visit_field(cx, field, reference)?;
        }
        self.walk_ty(visitor, cx, field.ty);
        if self.post() {
            visitor.visit_field(cx, field, reference)?;
        }
        ControlFlow::Continue(())
    }

    fn walk_function<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        program: Program,
        cx: &ItemContext,
        function: Function,
    ) -> ControlFlow<T> {
        walk_function(self, self.db, visitor, program, cx, function)
    }

    fn walk_ty<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        ty: Type,
    ) -> ControlFlow<T> {
        if self.pre() {
            visitor.visit_ty(cx, ty)?;
        }

        match ty.data(self.db) {
            TypeData::Error | TypeData::Void | TypeData::Primitive(_) | TypeData::Null => {}
            TypeData::Ghost(inner)
            | TypeData::Ref { inner, .. }
            | TypeData::List(inner)
            | TypeData::Range(inner)
            | TypeData::Optional(inner) => {
                self.walk_ty(visitor, cx, *inner)?;
            }
            TypeData::Struct(_) => {}
            TypeData::Function {
                params, return_ty, ..
            } => {
                for param in params.iter() {
                    self.walk_ty(visitor, cx, param.ty)?;
                }
                self.walk_ty(visitor, cx, *return_ty)?;
            }
        }
        if self.post() {
            visitor.visit_ty(cx, ty)?;
        }
        ControlFlow::Continue(())
    }

    fn walk_decreases<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        decreases: Decreases,
    ) -> ControlFlow<T> {
        if self.pre() {
            visitor.visit_decreases(cx, decreases)?;
        }
        match decreases {
            Decreases::Expr(expr) => self.walk_expr(visitor, cx, expr)?,
            Decreases::Unspecified | Decreases::Inferred => {}
        }
        if self.post() {
            visitor.visit_decreases(cx, decreases)?;
        }
        ControlFlow::Continue(())
    }

    fn walk_exprs<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        exprs: &[ExprIdx],
    ) -> ControlFlow<T> {
        for expr in exprs {
            self.walk_expr(visitor, cx, *expr)?;
        }
        ControlFlow::Continue(())
    }
    fn walk_expr<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        expr: ExprIdx,
    ) -> ControlFlow<T> {
        if self.pre() {
            visitor.visit_expr(cx, expr)?;
        }

        match &cx.expr(expr).data {
            ExprData::Literal(_) | ExprData::Missing | ExprData::Result => {}
            ExprData::Ident(var) => {
                visitor.visit_var(cx, *var)?;
            }
            ExprData::Field {
                expr,
                field,
                field_name,
                ..
            } => {
                self.walk_expr(visitor, cx, *expr)?;
                if let Some(field) = field {
                    self.walk_field(visitor, cx, field, field_name)?;
                }
            }
            ExprData::Struct { fields, .. } => {
                for f in fields {
                    self.walk_field(visitor, cx, &f.decl, &f.name)?;
                    self.walk_expr(visitor, cx, f.value)?;
                }
            }
            ExprData::If(if_expr) => {
                self.walk_if_expr(visitor, cx, if_expr)?;
            }
            ExprData::Call { expr, args } => {
                self.walk_expr(visitor, cx, *expr)?;
                for arg in args {
                    self.walk_expr(visitor, cx, *arg)?;
                }
            }
            ExprData::Bin { lhs, op: _, rhs } => {
                self.walk_expr(visitor, cx, *lhs)?;
                self.walk_expr(visitor, cx, *rhs)?;
            }
            ExprData::Unary { op: _, inner } => {
                self.walk_expr(visitor, cx, *inner)?;
            }
            ExprData::Ref { expr, .. } => {
                self.walk_expr(visitor, cx, *expr)?;
            }
            &ExprData::Index { base, index } => {
                self.walk_expr(visitor, cx, base)?;
                self.walk_expr(visitor, cx, index)?;
            }
            &ExprData::Range { lhs, rhs } => {
                if let Some(e) = lhs {
                    self.walk_expr(visitor, cx, e)?;
                }
                if let Some(e) = rhs {
                    self.walk_expr(visitor, cx, e)?;
                }
            }
            ExprData::List { elems } => {
                for elem in elems {
                    self.walk_expr(visitor, cx, *elem)?;
                }
            }
            ExprData::Quantifier { params, expr, .. } => {
                self.walk_param_list(visitor, cx, params)?;
                self.walk_expr(visitor, cx, *expr)?;
            }
        };

        if self.post() {
            visitor.visit_expr(cx, expr)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_if_expr<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        if_expr: &IfExpr,
    ) -> ControlFlow<T> {
        self.walk_expr(visitor, cx, if_expr.condition)?;
        self.walk_block(visitor, cx, &if_expr.then_branch)?;
        match if_expr.else_branch.as_deref() {
            Some(Else::Block(block)) => self.walk_block(visitor, cx, block),
            Some(Else::If(if_expr)) => self.walk_if_expr(visitor, cx, if_expr),
            None => ControlFlow::Continue(()),
        }
    }

    fn walk_block<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        block: &Block,
    ) -> ControlFlow<T> {
        for stmt in &block.stmts {
            if self.pre() {
                visitor.visit_stmt(cx, stmt)?;
            }

            match &stmt.data {
                StatementData::Return(Some(expr)) => self.walk_expr(visitor, cx, *expr)?,
                StatementData::Return(None) => {}
                StatementData::Expr(expr) => self.walk_expr(visitor, cx, *expr)?,
                &StatementData::Let {
                    variable,
                    explicit_ty,
                    initializer,
                } => {
                    visitor.visit_var(cx, variable)?;
                    if let Some(ty) = explicit_ty {
                        self.walk_ty(visitor, cx, ty)?;
                    }
                    self.walk_expr(visitor, cx, initializer)?;
                }
                StatementData::While {
                    expr,
                    invariants,
                    decreases,
                    body,
                } => {
                    self.walk_expr(visitor, cx, *expr)?;
                    for inv in invariants {
                        self.walk_exprs(visitor, cx, inv)?;
                    }
                    self.walk_decreases(visitor, cx, *decreases)?;
                    self.walk_block(visitor, cx, body)?;
                }
                StatementData::Assertion { exprs, .. } => self.walk_exprs(visitor, cx, exprs)?,
            }

            if self.post() {
                visitor.visit_stmt(cx, stmt)?;
            }
        }

        if let Some(expr) = block.tail_expr {
            self.walk_expr(visitor, cx, expr)?;
        }

        ControlFlow::Continue(())
    }

    fn walk_param_list<T>(
        &mut self,
        visitor: &mut impl Visitor<T>,
        cx: &ItemContext,
        param_list: &ParamList,
    ) -> ControlFlow<T> {
        for param in &param_list.params {
            if self.pre() {
                visitor.visit_param(cx, param)?;
            }
            self.walk_ty(visitor, cx, param.ty)?;
            if self.post() {
                visitor.visit_param(cx, param)?;
            }
        }

        ControlFlow::Continue(())
    }
}

fn walk_program<T>(
    walker: &mut impl Walker,
    db: &dyn crate::Db,
    visitor: &mut impl Visitor<T>,
    program: Program,
) -> ControlFlow<T> {
    for item in program.items(db) {
        let Some(item) = ir::item(db, program, item.clone()) else { continue };
        let cx = ItemContext::new(db, program, item);
        match item {
            ir::Item::Type(ty_decl) => {
                walker.walk_ty_decl(visitor, program, &cx, ty_decl)?;
            }
            ir::Item::TypeInvariant(ty_inv) => {
                walker.walk_ty_inv(visitor, program, &cx, ty_inv)?;
            }
            ir::Item::Function(f) => {
                walker.walk_function(visitor, program, &cx, f)?;
            }
        }
    }
    ControlFlow::Continue(())
}

fn walk_function<T>(
    walker: &mut impl Walker,
    db: &dyn crate::Db,
    visitor: &mut impl Visitor<T>,
    program: Program,
    cx: &ItemContext,
    function: Function,
) -> ControlFlow<T> {
    let Some(fx) = cx.function_context() else { return ControlFlow::Continue(()) };

    {
        visitor.visit_var(cx, fx.function_var())?;

        walker.walk_param_list(visitor, cx, function.param_list(db))?;

        for it in fx.conditions() {
            walker.walk_exprs(visitor, cx, it.exprs())?;
        }

        walker.walk_decreases(visitor, cx, fx.decreases())?;

        if let Some(ret_ty) = function.ret(db) {
            walker.walk_ty(visitor, cx, ret_ty)?;
        }
    }

    let body = ir::function_body(db, program, function);
    if let Some((cx, body)) = body {
        walker.walk_block(visitor, &cx, &body)?;
    }

    ControlFlow::Continue(())
}
