use std::{iter, ops::ControlFlow, sync::Arc};

use mist_syntax::{
    ast::{self, Spanned},
    ptr::AstPtr,
    AstNode, SourceSpan, WalkEvent,
};

use crate::{
    def::{Def, DefKind, Function, Struct, StructField, TypeInvariant},
    file::SourceFile,
    hir::{
        self, Block, Decreases, ExprData, ExprIdx, IfExpr, ItemContext, ItemSourceMap,
        StatementData, StatementId, TypeSrc, VariableIdx, WhileExpr,
    },
    types::Field,
};

pub trait Walker<'db>: Sized {
    fn init(db: &'db dyn crate::Db, vcx: VisitContext) -> Self
    where
        Self:;
    #[must_use]
    fn walk_program<'v, V: Visitor>(
        db: &'db dyn crate::Db,
        file: SourceFile,
        visitor: &'v mut V,
    ) -> ControlFlow<V::Item> {
        for def in file.definitions(db) {
            Self::walk_def(db, file, visitor, def)?;
        }
        ControlFlow::Continue(())
    }
    #[must_use]
    fn walk_def<'v, V: Visitor>(
        db: &'db dyn crate::Db,
        file: SourceFile,
        visitor: &'v mut V,
        def: Def,
    ) -> ControlFlow<V::Item> {
        let Some(hir) = def.hir(db) else { return ControlFlow::Continue(()) };
        let cx = Arc::new(hir.cx(db).clone());
        let source_map = Arc::new(hir.source_map(db).clone());
        let vcx = VisitContext { cx, source_map: source_map.clone() };

        for event in def.syntax(db).preorder() {
            match event {
                WalkEvent::Enter(_) => {}
                WalkEvent::Leave(node) => {
                    if let Some(n) = ast::NameOrNameRef::cast(node.clone()) {
                        if let Some(named) = source_map.name_var(&AstPtr::new(&n)) {
                            match named {
                                hir::Named::Variable(var) => {
                                    visitor.visit_var(&vcx, var, n.span())?;
                                }
                                hir::Named::StructField(field) => {
                                    visitor.visit_struct_field(&vcx, field, &n)?;
                                }
                            }
                        }
                    }
                    if let Some(t) = ast::Type::cast(node) {
                        if let Some(ty) = source_map.ty_ast((&t).into()) {
                            visitor.visit_ty(&vcx, ty)?;
                        }
                    }
                }
            }
        }

        let mut walker = Self::init(db, vcx.clone());
        match def.kind(db) {
            DefKind::Struct(st) => {
                walker.walk_struct(visitor, st)?;
            }
            DefKind::StructField(_) => {
                // TODO: Should we walk it here?
                // walker.walk_struct(visitor, st)?;
            }
            DefKind::TypeInvariant(ty_inv) => {
                walker.walk_ty_inv(visitor, file, ty_inv)?;
            }
            DefKind::Function(f) => {
                walker.walk_function(visitor, f)?;
            }
        }
        ControlFlow::Continue(())
    }
    #[must_use]
    fn walk_struct<V: Visitor>(&mut self, visitor: &mut V, st: Struct) -> ControlFlow<V::Item>;
    #[must_use]
    fn walk_ty_inv<V: Visitor>(
        &mut self,
        visitor: &mut V,
        file: SourceFile,
        ty_inv: TypeInvariant,
    ) -> ControlFlow<V::Item>;
    #[must_use]
    fn walk_field<V: Visitor>(
        &mut self,
        visitor: &mut V,
        field: Field,
        reference: &ast::NameOrNameRef,
    ) -> ControlFlow<V::Item>;
    #[must_use]
    fn walk_struct_field<V: Visitor>(
        &mut self,
        visitor: &mut V,
        field: StructField,
        reference: &ast::NameOrNameRef,
    ) -> ControlFlow<V::Item>;
    #[must_use]
    fn walk_function<V: Visitor>(
        &mut self,
        visitor: &mut V,
        function: Function,
    ) -> ControlFlow<V::Item>;
    #[must_use]
    fn walk_decreases<V: Visitor>(
        &mut self,
        visitor: &mut V,
        decreases: Decreases,
    ) -> ControlFlow<V::Item>;
    #[must_use]
    fn walk_exprs<V: Visitor>(
        &mut self,
        visitor: &mut V,
        exprs: &[ExprIdx],
    ) -> ControlFlow<V::Item>;
    #[must_use]
    fn walk_expr<V: Visitor>(&mut self, visitor: &mut V, expr: ExprIdx) -> ControlFlow<V::Item>;
    #[must_use]
    fn walk_if_expr<V: Visitor>(
        &mut self,
        visitor: &mut V,
        if_expr: &IfExpr,
    ) -> ControlFlow<V::Item>;
    #[must_use]
    fn walk_block<V: Visitor>(&mut self, visitor: &mut V, block: &Block) -> ControlFlow<V::Item>;
}

#[derive(Clone)]
pub struct VisitContext {
    pub cx: Arc<ItemContext>,
    pub source_map: Arc<ItemSourceMap>,
}

#[allow(unused)]
pub trait Visitor {
    type Item;

    #[must_use]
    fn visit_ty_decl(&mut self, vcx: &VisitContext, st: Struct) -> ControlFlow<Self::Item> {
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
    fn visit_struct_field(
        &mut self,
        vcx: &VisitContext,
        field: StructField,
        reference: &ast::NameOrNameRef,
    ) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_field(
        &mut self,
        vcx: &VisitContext,
        field: Field,
        reference: &ast::NameOrNameRef,
    ) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_var(
        &mut self,
        vcx: &VisitContext,
        var: VariableIdx,
        span: SourceSpan,
    ) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_self(
        &mut self,
        vcx: &VisitContext,
        src: &hir::SpanOrAstPtr<ast::Expr>,
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
    fn visit_ty(&mut self, vcx: &VisitContext, ty: TypeSrc) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
    #[must_use]
    fn visit_stmt(&mut self, vcx: &VisitContext, stmt: StatementId) -> ControlFlow<Self::Item> {
        ControlFlow::Continue(())
    }
}

pub struct OrderedWalk<'db, O> {
    _db: &'db dyn crate::Db,
    root: ast::SourceFile,
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
        let root = vcx.cx.def().file(db).root(db);
        Self { _db: db, root, vcx, order: O::default() }
    }

    #[must_use]
    fn walk_struct<V: Visitor>(&mut self, visitor: &mut V, s: Struct) -> ControlFlow<V::Item> {
        if self.pre() {
            visitor.visit_ty_decl(&self.vcx, s)?;
        }
        // TODO
        // for f in s.fields(self.db) {
        //     let f_ast = f.ast_node(self.db);
        //     if let Some(name) = f_ast.name() {
        //         self.walk_field(visitor, f.into(), &ast::NameOrNameRef::Name(name))?
        //     }
        // }
        if self.post() {
            visitor.visit_ty_decl(&self.vcx, s)?;
        }
        ControlFlow::Continue(())
    }

    #[must_use]
    fn walk_ty_inv<V: Visitor>(
        &mut self,
        visitor: &mut V,
        _program: SourceFile,
        _ty_inv: TypeInvariant,
    ) -> ControlFlow<V::Item> {
        if let Some(body_expr) = self.vcx.cx.body_expr() {
            self.walk_expr(visitor, body_expr)?;
        }
        ControlFlow::Continue(())
    }

    #[must_use]
    fn walk_field<V: Visitor>(
        &mut self,
        visitor: &mut V,
        field: Field,
        reference: &ast::NameOrNameRef,
    ) -> ControlFlow<V::Item> {
        visitor.visit_field(&self.vcx, field, reference)?;
        match field {
            Field::AdtField(adt_field) => match adt_field.kind() {
                crate::types::AdtFieldKind::StructField(sf) => {
                    self.walk_struct_field(visitor, sf, reference)?;
                }
            },
            Field::Builtin(_) => {}
            Field::Undefined => {}
        }
        ControlFlow::Continue(())
    }

    #[must_use]
    fn walk_struct_field<V: Visitor>(
        &mut self,
        visitor: &mut V,
        field: StructField,
        reference: &ast::NameOrNameRef,
    ) -> ControlFlow<V::Item> {
        visitor.visit_struct_field(&self.vcx, field, reference)
    }

    #[must_use]
    fn walk_function<V: Visitor>(
        &mut self,
        visitor: &mut V,
        _function: Function,
    ) -> ControlFlow<V::Item> {
        let Some(fx) = self.vcx.cx.function_context().cloned() else { return ControlFlow::Continue(()) };

        for it in fx.conditions() {
            self.walk_exprs(visitor, it.exprs())?;
        }

        self.walk_decreases(visitor, fx.decreases())?;

        if let Some(body_expr) = self.vcx.cx.body_expr() {
            self.walk_expr(visitor, body_expr)?;
        }

        ControlFlow::Continue(())
    }

    #[must_use]
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

    #[must_use]
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
    #[must_use]
    fn walk_expr<V: Visitor>(&mut self, visitor: &mut V, expr: ExprIdx) -> ControlFlow<V::Item> {
        if self.pre() {
            visitor.visit_expr(&self.vcx, expr)?;
        }

        let expr_src = self.vcx.source_map.expr_src(&self.vcx.cx, expr);

        match self.vcx.cx.original_expr(expr).data.clone() {
            ExprData::Literal(_) | ExprData::Missing | ExprData::Result => {}
            ExprData::Ident(_) => {}
            ExprData::Self_ => visitor.visit_self(&self.vcx, &self.vcx.source_map[expr])?,
            ExprData::Field { expr: inner, field, .. } => {
                self.walk_expr(visitor, inner)?;

                // TODO: This should be replaced with a try-block when stable
                let res: Option<_> = (|| {
                    let src: ast::FieldExpr =
                        expr_src.into_ptr()?.cast()?.to_node(self.root.syntax());
                    let field_ref = src.field()?.into();
                    Some(visitor.visit_field(&self.vcx, field, &field_ref))
                })();
                if let Some(res) = res {
                    res?;
                }
            }
            ExprData::Adt { fields, .. } => {
                let src_fields = expr_src
                    .into_ptr()
                    .and_then(|expr| match expr.to_node(self.root.syntax()) {
                        ast::Expr::StructExpr(it) => {
                            Some(it.fields().map(Some).chain(iter::repeat(None)))
                        }
                        _ => None,
                    })
                    .into_iter()
                    .flatten();

                for (f, f_ast) in iter::zip(fields, src_fields) {
                    if let Some(name) = f_ast.and_then(|f_ast| f_ast.name_ref()) {
                        self.walk_field(visitor, f.decl.into(), &name.into())?;
                    }
                    self.walk_expr(visitor, f.value)?;
                }
            }
            ExprData::If(if_expr) => {
                self.walk_if_expr(visitor, &if_expr)?;
            }
            ExprData::While(WhileExpr { expr, invariants, decreases, body }) => {
                self.walk_expr(visitor, expr)?;
                for inv in &invariants {
                    self.walk_exprs(visitor, inv)?;
                }
                self.walk_decreases(visitor, decreases)?;
                self.walk_expr(visitor, body)?;
            }
            ExprData::For(for_expr) => {
                self.walk_expr(visitor, for_expr.in_expr)?;
                for inv in &for_expr.invariants {
                    self.walk_exprs(visitor, inv)?;
                }
                self.walk_expr(visitor, for_expr.body)?
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
            ExprData::NotNull(inner) => {
                self.walk_expr(visitor, inner)?;
            }
            ExprData::Quantifier { over, expr, .. } => {
                match over {
                    hir::QuantifierOver::Vars(_) => {
                        // NOTE: don't walk anything here, since it will be
                        // covered by walking the vars some other place
                    }
                    hir::QuantifierOver::In(_, expr) => self.walk_expr(visitor, expr)?,
                }

                self.walk_expr(visitor, expr)?;
            }
            ExprData::Builtin(b) => match b {
                hir::BuiltinExpr::RangeMin(r) | hir::BuiltinExpr::RangeMax(r) => {
                    self.walk_expr(visitor, r)?
                }
                hir::BuiltinExpr::InRange(idx, r) => {
                    self.walk_expr(visitor, idx)?;
                    self.walk_expr(visitor, r)?;
                }
            },
        };

        if self.post() {
            visitor.visit_expr(&self.vcx, expr)?;
        }

        ControlFlow::Continue(())
    }

    #[must_use]
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

    #[must_use]
    fn walk_block<V: Visitor>(&mut self, visitor: &mut V, block: &Block) -> ControlFlow<V::Item> {
        for &stmt in &block.stmts {
            if self.pre() {
                visitor.visit_stmt(&self.vcx, stmt)?;
            }

            match self.vcx.cx[stmt].data.clone() {
                StatementData::Expr(expr) => self.walk_expr(visitor, expr)?,
                StatementData::Let(let_stmt) => {
                    self.walk_expr(visitor, let_stmt.initializer)?;
                }
                StatementData::Assertion { exprs, .. } => self.walk_exprs(visitor, &exprs)?,
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
}
