use std::{collections::HashMap, ops::Deref, sync::Mutex};

use bitflags::bitflags;
use derive_new::new;
use miette::Diagnostic;
use mist_syntax::{
    ast::{
        self,
        operators::{ArithOp, BinaryOp, CmpOp},
        HasAttrs, HasName, Spanned,
    },
    SourceSpan,
};
use thiserror::Error;
use tracing::error;

use crate::hir::{
    self, AssertionKind, Block, Condition, Decreases, Expr, ExprData, ExprIdx, Field, FieldParent,
    Ident, IfExpr, ItemId, Literal, Param, Primitive, Program, Quantifier, Statement,
    StatementData, StructExprField, TypeData, TypeId, Variable, VariableId, VariableIdx,
    VariableRef,
};

use super::{
    item_context::{FunctionContext, SpanOrAstPtr},
    ItemContext, ItemSourceMap, TypeSrc, TypeSrcId,
};

fn id<T>(t: T) -> T {
    t
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VariableDeclarationKind {
    Let,
    Parameter,
    Function,
    Undefined,
}

#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariableDeclaration {
    name: Ident,
    kind: VariableDeclarationKind,
}

impl VariableDeclaration {
    pub(crate) fn new_let(name: impl Into<Ident>) -> Self {
        VariableDeclaration::new(name.into(), VariableDeclarationKind::Let)
    }
    pub(crate) fn new_param(name: impl Into<Ident>) -> Self {
        VariableDeclaration::new(name.into(), VariableDeclarationKind::Parameter)
    }
    pub(crate) fn new_function(name: impl Into<Ident>) -> Self {
        VariableDeclaration::new(name.into(), VariableDeclarationKind::Function)
    }
    pub(crate) fn new_undefined(name: impl Into<Ident>) -> Self {
        VariableDeclaration::new(name.into(), VariableDeclarationKind::Undefined)
    }

    pub fn name(&self) -> &Ident {
        &self.name
    }

    pub fn kind(&self) -> VariableDeclarationKind {
        self.kind
    }
}

impl Spanned for &'_ VariableDeclaration {
    fn span(self) -> SourceSpan {
        self.name.span()
    }
}

impl TypeId {
    pub(super) fn tc_strip_ghost(self, tc: &mut TypeChecker) -> TypeId {
        match tc.ty_table.lock().unwrap().inlined_probe_value(self) {
            TypeData::Ghost(inner) => inner,
            _ => self,
        }
    }
    pub(super) fn with_ghost(self, ghost: bool) -> impl Typed + Copy {
        Ghosted(self, ghost)
    }
    pub(super) fn ghost(self) -> impl Typed + Copy {
        self.with_ghost(true)
    }
    pub(super) fn tc_is_ghost(self, tc: &mut TypeChecker) -> bool {
        matches!(
            tc.ty_table.lock().unwrap().inlined_probe_value(self),
            TypeData::Ghost(_)
        )
    }
}

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct ScopeFlags: u32 {
        const NONE = 0b00;
        const GHOST = 0b01;
    }
}

impl ScopeFlags {
    pub fn is_ghost(self) -> bool {
        self.contains(Self::GHOST)
    }
}
impl Default for ScopeFlags {
    fn default() -> Self {
        Self::NONE
    }
}

#[derive(Debug, Default, Clone)]
pub struct Scope {
    flags: ScopeFlags,
    vars: HashMap<String, VariableIdx>,
}

impl Scope {
    pub fn is_ghost(&self) -> bool {
        self.flags.is_ghost()
    }
    pub fn insert(&mut self, name: String, var: VariableIdx) {
        self.vars.insert(name, var);
    }
    pub fn get(&mut self, name: &str) -> Option<VariableIdx> {
        self.vars.get(name).copied()
    }
}

pub struct TypeChecker<'w> {
    db: &'w dyn crate::Db,
    program: Program,
    root: &'w ast::SourceFile,
    return_ty: Option<TypeSrcId>,
    scope: Scope,
    scope_stack: Vec<Scope>,
    source_map: ItemSourceMap,
    pub(super) cx: ItemContext,

    ty_table: Mutex<ena::unify::InPlaceUnificationTable<TypeId>>,
    ty_cache: HashMap<TypeData, TypeId>,
    ty_keys: Vec<TypeId>,
}

impl From<TypeChecker<'_>> for (ItemContext, ItemSourceMap) {
    fn from(mut tc: TypeChecker<'_>) -> Self {
        for &ty in &tc.ty_keys {
            let td = tc.ty_table.lock().unwrap().probe_value(ty);
            tc.cx.ty_table.insert(ty.0, td);
        }

        (tc.cx, tc.source_map)
    }
}

impl<'a> TypeChecker<'a> {
    pub(crate) fn init(
        db: &'a dyn crate::Db,
        program: Program,
        root: &'a ast::SourceFile,
        id: ItemId,
        function: Option<hir::Function>,
    ) -> Self {
        let mut ty_table = ena::unify::InPlaceUnificationTable::default();
        let mut ty_cache = HashMap::new();
        let mut ty_keys = vec![];
        let mut cache = |td: TypeData| {
            let key = ty_table.new_key(td.clone());
            ty_cache.insert(td, key);
            ty_keys.push(key);
            key
        };
        cache(TypeData::Primitive(Primitive::Bool));
        let int_ty = cache(TypeData::Primitive(Primitive::Int));
        cache(TypeData::Void);
        cache(TypeData::Null);
        let error_ty = cache(TypeData::Error);
        let mut checker = Self {
            db,
            program,
            root,
            ty_table: Mutex::new(ty_table),
            ty_cache,
            ty_keys,
            return_ty: None,
            scope: Default::default(),
            scope_stack: vec![],
            source_map: Default::default(),
            cx: ItemContext::new(id, error_ty, int_ty),
        };

        let is_ghost = if let Some(f) = function {
            f.attrs(db).is_ghost()
        } else {
            false
        };

        if is_ghost {
            checker = checker.ghosted();
        }

        for &item_id in program.items(db) {
            let f = match hir::item(db, program, root, item_id) {
                Some(hir::Item::Function(f)) => f,
                Some(hir::Item::Type(t)) => match t.data(db) {
                    hir::TypeDeclData::Struct(s) => {
                        let s_ty = *checker
                            .cx
                            .named_types
                            .entry(t.name(db).to_string())
                            .or_insert_with(|| {
                                let key = checker
                                    .ty_table
                                    .lock()
                                    .unwrap()
                                    .new_key(TypeData::Struct(s));
                                checker.ty_keys.push(key);
                                key
                            });
                        let ts = checker.alloc_type_src(
                            TypeSrc {
                                data: Some(TypeData::Struct(s)),
                                ty: s_ty,
                            },
                            s.name(db).span(),
                        );
                        checker.cx.struct_types.insert(s, ts);

                        let fields = hir::struct_fields(db, s)
                            .into_iter()
                            .map(|f| {
                                let data = f.ty(db, root);
                                (f, checker.expect_find_type_src(&data))
                            })
                            .collect();
                        checker.cx.structs.insert(s, fields);

                        continue;
                    }
                },
                _ => continue,
            };
            let is_ghost = f.attrs(db).is_ghost();

            let params = f
                .param_list(db, root)
                .map(|param| {
                    let ty = checker.expect_find_type_src(&param.ty);
                    Param {
                        is_ghost: param.is_ghost,
                        name: param.name,
                        ty: checker.ghostify(ty, is_ghost),
                    }
                })
                .collect();
            let return_ty_src = f.ret(db, root).map(|ty| {
                checker
                    .find_type_src(&ty)
                    .with_ghost(is_ghost)
                    .ts(&mut checker)
            });
            let return_ty = return_ty_src
                .map(|ts| checker.cx[ts].ty)
                .unwrap_or_else(|| checker.void())
                .with_ghost(is_ghost)
                .ty(&mut checker);

            let var_span = f.name(db).span();
            let ty = checker.ty_id(TypeData::Function {
                attrs: f.attrs(db),
                name: Some(f.name(db).clone()),
                params,
                return_ty,
            });
            let ts = checker.cx.ty_src_arena.alloc(TypeSrc { data: None, ty });
            let var = checker.declare_variable(
                VariableDeclaration::new_function(f.name(db).clone()),
                ts,
                var_span,
            );

            if Some(f) == function {
                checker.cx.function_context = Some(FunctionContext {
                    function_var: VariableRef::new(var, var_span),
                    decreases: Default::default(),
                    conditions: vec![],
                    return_ty_src,
                });
            }
        }

        if let Some(f) = function {
            checker.cx.params = f
                .param_list(db, root)
                .map(|p| {
                    let ty = checker
                        .expect_find_type_src(&p.ty)
                        .with_ghost(is_ghost)
                        .ts(&mut checker);
                    let var = checker.declare_variable(
                        VariableDeclaration::new_param(p.name.clone()),
                        ty,
                        match p.ty {
                            Some(ty) => SpanOrAstPtr::from(&ty),
                            None => SpanOrAstPtr::Span(p.name.span()),
                        },
                    );
                    Param {
                        is_ghost: p.is_ghost,
                        name: var,
                        ty,
                    }
                })
                .collect();

            checker.return_ty = f.ret(db, root).map(|ty| {
                let ty = checker.find_type_src(&ty);
                checker.ghostify(ty, is_ghost)
            });

            let conditions = f
                .conditions(db, root)
                .map(|c| match c {
                    ast::Condition::Requires(r) => {
                        Condition::Requires(checker.check_boolean_exprs(r.comma_exprs()))
                    }
                    ast::Condition::Ensures(r) => {
                        Condition::Ensures(checker.check_boolean_exprs(r.comma_exprs()))
                    }
                })
                .collect();

            let decreases = checker.check_decreases(f.decreases(db, root));

            if let Some(cx) = &mut checker.cx.function_context {
                cx.conditions = conditions;
                cx.decreases = decreases;
            }
        }

        checker
    }

    pub fn ty_id(&mut self, td: TypeData) -> TypeId {
        let key = *self.ty_cache.entry(td).or_insert_with_key(|td| {
            let key = self.ty_table.lock().unwrap().new_key(td.clone());
            self.ty_keys.push(key);
            key
        });
        key
    }

    pub fn bool(&self) -> TypeId {
        self.ty_cache[&TypeData::Primitive(Primitive::Bool)]
    }
    pub fn ghost_bool(&mut self) -> TypeId {
        self.bool().with_ghost(true).ty(self)
    }
    pub fn int(&self) -> TypeId {
        self.ty_cache[&TypeData::Primitive(Primitive::Int)]
    }
    pub fn void(&self) -> TypeId {
        self.ty_cache[&TypeData::Void]
    }
    fn null_ty(&self) -> TypeId {
        self.ty_cache[&TypeData::Null]
    }
    fn error_ty(&self) -> TypeId {
        self.ty_cache[&TypeData::Error]
    }

    pub fn set_body_expr_from_block(&mut self, block: Block, node: ast::BlockExpr) {
        let idx = self.alloc_expr(
            Expr::new(block.return_ty, ExprData::Block(block)),
            &ast::Expr::from(node),
        );
        self.cx.body_expr = Some(idx);
    }
    pub fn set_return_ty(&mut self, ty: TypeSrcId) {
        self.cx.return_ty = Some(ty);
    }

    pub fn ghosted(mut self) -> Self {
        debug_assert!(
            self.scope_stack.is_empty(),
            "Tried to make a checker ghost, while it was in operation"
        );
        if let Some(ty) = self.return_ty {
            self.return_ty = Some(self.ghostify(ty, true));
        }
        self.scope.flags |= ScopeFlags::GHOST;
        self
    }
    fn push_scope(&mut self, f: impl FnOnce(ScopeFlags) -> ScopeFlags) {
        self.scope_stack.push(self.scope.clone());
        self.scope.flags = f(self.scope.flags);
    }
    fn pop_scope(&mut self) {
        self.scope = self
            .scope_stack
            .pop()
            .expect("tried to pop scope while none was pushed");
    }
    fn check_if_expr(&mut self, if_expr: ast::IfExpr) -> ExprIdx {
        let condition = self.check(if_expr.span(), if_expr.condition());

        let condition_ty = self.expr_ty(condition);
        let is_ghost = condition_ty.tc_is_ghost(self);
        if is_ghost {
            self.expect_ty(
                if_expr
                    .condition()
                    .map(|e| e.span())
                    .unwrap_or_else(|| if_expr.span()),
                self.bool().ghost(),
                condition_ty,
            );
        } else {
            self.expect_ty(
                if_expr
                    .condition()
                    .map(|e| e.span())
                    .unwrap_or_else(|| if_expr.span()),
                self.bool(),
                condition_ty,
            );
        }

        let (then_branch, then_ty) = if let Some(then_branch) = if_expr.then_branch() {
            let block = self.check_block(&then_branch, |f| {
                if is_ghost {
                    f | ScopeFlags::GHOST
                } else {
                    f
                }
            });
            let ty = block.return_ty;
            (
                self.alloc_expr(Expr::new(ty, ExprData::Block(block)), then_branch.span()),
                ty,
            )
        } else {
            todo!()
        };
        let (else_branch, else_tail_span) = if_expr
            .else_branch()
            .map(|else_branch| match else_branch {
                ast::IfExprElse::IfExpr(e) => (self.check_if_expr(e), None),
                ast::IfExprElse::BlockExpr(b) => {
                    let block =
                        self.check_block(&b, |f| if is_ghost { f | ScopeFlags::GHOST } else { f });
                    let tail_span = block
                        .tail_expr
                        .map(|e| self.expr_span(e))
                        .or_else(|| block.stmts.last().map(|s| s.span));
                    let expr = self
                        .alloc_expr(Expr::new(block.return_ty, ExprData::Block(block)), b.span());
                    (expr, tail_span)
                }
            })
            .unzip();
        // TODO: tail_span should perhaps be a general concept for exprs, to
        // provide better spans in more cases
        let else_tail_span = else_tail_span.flatten();

        let ty = if let Some(b) = else_branch {
            let span = else_tail_span.unwrap_or_else(|| if_expr.span());
            let then_ty = then_ty.with_ghost(is_ghost);
            self.unify(span, then_ty, self.expr_ty(b))
        } else {
            let else_ty = self.void().with_ghost(is_ghost);
            self.expect_ty(if_expr.span(), then_ty, else_ty)
        };

        let result = IfExpr {
            if_span: if_expr.if_token().unwrap().span(),
            is_ghost,
            return_ty: ty,
            condition,
            then_branch,
            else_branch,
        };
        self.alloc_expr(
            Expr::new(result.return_ty, ExprData::If(result)),
            if_expr.span(),
        )
    }
    pub fn expr_ty(&self, expr: ExprIdx) -> TypeId {
        self.cx.expr_arena[expr].ty
    }
    pub fn expr_span(&self, expr: ExprIdx) -> SourceSpan {
        self.source_map.expr_map_back[expr].span()
    }
    pub fn check(&mut self, fallback_span: SourceSpan, expr: Option<ast::Expr>) -> ExprIdx {
        let expr = if let Some(expr) = expr {
            expr
        } else {
            return self.expr_error(
                fallback_span,
                None,
                None,
                TypeCheckErrorKind::MissingExpression,
            );
        };

        let new = match &expr {
            ast::Expr::Literal(it) => match it.kind() {
                ast::LiteralKind::IntNumber(s) => Expr::new(
                    self.int().with_ghost(self.scope.is_ghost()).ty(self),
                    ExprData::Literal(Literal::Int(s.to_string().parse().unwrap())),
                ),
                ast::LiteralKind::Bool(b) => Expr::new(
                    self.bool().with_ghost(self.scope.is_ghost()).ty(self),
                    ExprData::Literal(Literal::Bool(b)),
                ),
            },
            ast::Expr::IfExpr(it) => return self.check_if_expr(it.clone()),
            ast::Expr::WhileExpr(_) => todo!(),
            ast::Expr::PrefixExpr(it) => {
                let (_op_token, op) = if let Some(op) = it.op_details() {
                    op
                } else {
                    todo!("{it:#?}")
                };
                let inner = self.check(it.span(), it.expr());
                let inner_span = self.expr_span(inner);
                let inner_ty = self.expr_ty(inner);

                let is_ghost = self.is_ghost(inner);

                let ty: TypeId = match op {
                    ast::operators::UnaryOp::Not => {
                        self.expect_ty(inner_span, self.bool(), inner_ty);
                        self.bool()
                    }
                    ast::operators::UnaryOp::Neg => {
                        self.expect_ty(inner_span, self.int(), inner_ty);
                        self.int()
                    }
                };

                let ty = if is_ghost { ty.ghost().ty(self) } else { ty };

                Expr::new(ty, ExprData::Unary { op, inner })
            }
            ast::Expr::BlockExpr(it) => {
                let block = self.check_block(it, |f| f);
                Expr::new(block.return_ty, ExprData::Block(block))
            }
            ast::Expr::ReturnExpr(it) => {
                if let Some(expr) = it.expr() {
                    let expr_span = expr.span();
                    let expr_idx = self.check(expr.span(), Some(expr));

                    let return_ty = self.return_ty();
                    self.expect_ty(expr_span, return_ty, self.expr_ty(expr_idx));

                    // TODO: These properly should not be Error
                    Expr::new(self.error_ty(), ExprData::Return(Some(expr_idx)))
                } else {
                    Expr::new(self.error_ty(), ExprData::Return(None))
                }
            }
            ast::Expr::BinExpr(it) => {
                let lhs = self.check(it.span(), it.lhs());
                let (_op_token, op) = if let Some(op) = it.op_details() {
                    op
                } else {
                    todo!()
                };
                let rhs = self.check(it.span(), it.rhs());

                let lhs_ty = self.expr_ty(lhs).tc_strip_ghost(self);
                let rhs_ty = self.expr_ty(rhs).tc_strip_ghost(self);

                let is_ghost = self.is_ghost(lhs) || self.is_ghost(rhs);
                let int_ty = self.int();
                let bool_ty = self.bool();

                let ty = match op {
                    BinaryOp::LogicOp(_) => {
                        self.expect_ty(it.span(), bool_ty, lhs_ty);
                        self.expect_ty(it.span(), bool_ty, rhs_ty);
                        bool_ty
                    }
                    BinaryOp::CmpOp(CmpOp::Eq { .. }) => {
                        self.unify(it.span(), lhs_ty, rhs_ty);
                        self.bool()
                    }
                    BinaryOp::CmpOp(CmpOp::Ord { .. }) => {
                        self.expect_ty(it.span(), int_ty, lhs_ty);
                        self.expect_ty(it.span(), int_ty, rhs_ty);
                        self.bool()
                    }
                    BinaryOp::ArithOp(op) => match op {
                        ArithOp::Add => match self.ty_data(lhs_ty) {
                            TypeData::Primitive(Primitive::Int) => {
                                self.expect_ty(self.expr_span(rhs), lhs_ty, rhs_ty)
                            }
                            TypeData::List(_) => {
                                self.expect_ty(self.expr_span(rhs), lhs_ty, rhs_ty)
                            }
                            _ => self.push_error(
                                it.span(),
                                None,
                                None,
                                TypeCheckErrorKind::NotYetImplemented(format!(
                                    "addition of '{}' and '{}'",
                                    self.pretty_ty(lhs_ty),
                                    self.pretty_ty(rhs_ty)
                                )),
                            ),
                        },
                        ArithOp::Mul
                        | ArithOp::Sub
                        | ArithOp::Div
                        | ArithOp::Rem
                        | ArithOp::Shl
                        | ArithOp::Shr
                        | ArithOp::BitXor
                        | ArithOp::BitOr
                        | ArithOp::BitAnd => {
                            self.expect_ty(it.span(), int_ty, lhs_ty);
                            self.expect_ty(it.span(), int_ty, rhs_ty);
                            self.int()
                        }
                    },
                    BinaryOp::Assignment => {
                        let span = it.rhs().map(|rhs| rhs.span()).unwrap_or(it.span());

                        if !self.is_ghost(lhs) && (self.is_ghost(rhs) || self.scope.is_ghost()) {
                            // NOTE: Assignment from ghost to non-ghost
                            self.push_error(
                                self.expr_span(rhs),
                                None,
                                None,
                                TypeCheckErrorKind::GhostAssignedToNonGhost,
                            );
                        }

                        self.expect_ty(span, lhs_ty, rhs_ty)
                    }
                };

                let ty = if is_ghost { ty.ghost().ty(self) } else { ty };

                Expr::new(ty, ExprData::Bin { lhs, op, rhs })
            }
            ast::Expr::CallExpr(it) => {
                let fn_expr = self.check(it.span(), it.expr());
                let args: Vec<_> = it
                    .arg_list()
                    .unwrap()
                    .args()
                    .map(|arg| self.check(arg.span(), arg.expr()))
                    .collect();

                match self.ty_data(self.expr_ty(fn_expr)) {
                    TypeData::Function {
                        attrs,
                        name: _,
                        params,
                        return_ty,
                    } => {
                        let mut ghostify_pure = false;

                        if self.scope.is_ghost() {
                            if !(attrs.is_ghost() || attrs.is_pure()) {
                                self.push_error(
                                    it.span(),
                                    None,
                                    None,
                                    TypeCheckErrorKind::NonGhostNorPureCalledInGhost,
                                );
                            }

                            if attrs.is_pure() {
                                ghostify_pure = true;
                            }
                        }

                        if args.len() != params.len() {
                            return self.expr_error(
                                it.expr()
                                    .as_ref()
                                    .map(SpanOrAstPtr::from)
                                    .unwrap_or_else(|| it.span().into()),
                                None,
                                None,
                                TypeCheckErrorKind::NotYetImplemented(
                                    "argument count mismatch".to_string(),
                                ),
                            );
                        }
                        for (a, b) in args.iter().zip(params.iter().map(|p| p.ty)) {
                            let b = self.cx[b].ty;
                            let expected = b.with_ghost(ghostify_pure);
                            self.expect_ty(self.expr_span(*a), expected, self.cx.expr_arena[*a].ty);
                        }

                        Expr {
                            ty: return_ty.with_ghost(ghostify_pure).ty(self),
                            data: ExprData::Call {
                                expr: fn_expr,
                                args,
                            },
                        }
                    }
                    TypeData::Error => Expr {
                        ty: self.error_ty(),
                        data: ExprData::Call {
                            expr: fn_expr,
                            args,
                        },
                    },
                    t => todo!("`{t:?}` is not a function"),
                }
            }
            ast::Expr::RangeExpr(it) => {
                let lhs = it.lhs().map(|lhs| self.check(lhs.span(), Some(lhs)));
                let rhs = it.rhs().map(|rhs| self.check(rhs.span(), Some(rhs)));

                let ty = match (lhs, rhs) {
                    (None, None) => {
                        return self.expr_error(
                            &expr,
                            None,
                            None,
                            TypeCheckErrorKind::NotYetImplemented("inference of '..'".to_string()),
                        )
                    }
                    (None, Some(x)) | (Some(x), None) => {
                        let x_ty = self.expr_ty(x);
                        let actual = x_ty.tc_strip_ghost(self);
                        self.expect_ty(self.expr_span(x), self.int(), actual);
                        x_ty
                    }
                    (Some(lhs), Some(rhs)) => {
                        let lhs_ty = self.expr_ty(lhs);
                        let lhs_ty_no_ghost = lhs_ty.tc_strip_ghost(self);
                        let rhs_ty = self.expr_ty(rhs);
                        let rhs_ty_no_ghost = rhs_ty.tc_strip_ghost(self);
                        self.expect_ty(self.expr_span(lhs), self.int(), lhs_ty_no_ghost);
                        self.expect_ty(self.expr_span(rhs), self.int(), rhs_ty_no_ghost);
                        lhs_ty
                    }
                };

                Expr::new(
                    self.ty_id(TypeData::Range(ty)),
                    ExprData::Range { lhs, rhs },
                )
            }
            ast::Expr::IndexExpr(it) => {
                let base = self.check(it.span(), it.base());
                let index = self.check(it.span(), it.index());

                let base_ty = self.expr_ty(base);
                let index_ty = self.expr_ty(index);

                let is_ghost = base_ty.tc_is_ghost(self) || index_ty.tc_is_ghost(self);

                let is_range = match self.ty_data(index_ty) {
                    TypeData::Primitive(Primitive::Int) => false,
                    TypeData::Range(idx) => {
                        self.expect_ty(it.span(), self.int().ghost(), idx);
                        true
                    }
                    _ => {
                        self.expect_ty(it.span(), self.int().ghost(), index_ty);
                        false
                    }
                };

                let base_ty_no_ghost = base_ty.tc_strip_ghost(self);
                match self.ty_data(base_ty_no_ghost) {
                    TypeData::List(elem_ty) => {
                        if is_range {
                            Expr::new(
                                base_ty.with_ghost(is_ghost).ty(self),
                                ExprData::Index { base, index },
                            )
                        } else {
                            Expr::new(
                                elem_ty.with_ghost(is_ghost).ty(self),
                                ExprData::Index { base, index },
                            )
                        }
                    }
                    _ => {
                        return self.expr_error(
                            &expr,
                            None,
                            None,
                            TypeCheckErrorKind::NotYetImplemented(format!(
                                "index into {}",
                                self.pretty_ty(self.expr_ty(base))
                            )),
                        )
                    }
                }
            }
            ast::Expr::ListExpr(it) => {
                let mut elem_ty = None;
                let elems: Vec<_> = it
                    .comma_exprs()
                    .map(|comma_expr| {
                        let expr = self.check(comma_expr.span(), comma_expr.expr());
                        if let Some(t) = elem_ty {
                            self.expect_ty(comma_expr.span(), t, self.expr_ty(expr));
                        } else {
                            elem_ty = Some(self.expr_ty(expr));
                        }
                        expr
                    })
                    .collect();

                if let Some(ty) = elem_ty {
                    let inner_ty_no_ghost = ty.tc_strip_ghost(self);
                    Expr::new(
                        self.ty_id(TypeData::List(inner_ty_no_ghost))
                            .with_ghost(ty.tc_is_ghost(self))
                            .ty(self),
                        ExprData::List { elems },
                    )
                } else {
                    let elem_ty = self.new_free();
                    Expr::new(
                        self.ty_id(TypeData::List(elem_ty)),
                        ExprData::List { elems },
                    )
                }
            }
            ast::Expr::FieldExpr(it) => {
                let expr = self.check(it.span(), it.expr());
                let field = if let Some(field) = it.field() {
                    Ident::from(field)
                } else {
                    todo!()
                };

                let expr_ty = self.expr_ty(expr);
                let expr_ty_no_ghost = expr_ty.tc_strip_ghost(self);
                let (sf, field_ty): (Option<Field>, TypeId) = match self.ty_data(expr_ty_no_ghost) {
                    TypeData::Error => (None, self.error_ty()),
                    TypeData::Ref { is_mut, inner } => match self.ty_data(inner) {
                        TypeData::Struct(s) => {
                            let fields = self.struct_fields(s);
                            if let Some(field) =
                                fields.iter().find(|f| f.name.as_str() == field.as_str())
                            {
                                (
                                    Some(field.clone()),
                                    self.expect_find_type(&field.ty(self.db, self.root)),
                                )
                            } else {
                                return self.expr_error(
                                    field.span(),
                                    None,
                                    None,
                                    TypeCheckErrorKind::UnknownStructField {
                                        field,
                                        strukt: s.name(self.db),
                                    },
                                );
                            }
                        }
                        _ => {
                            self.push_error(
                                it.field().map(|f| f.span()).unwrap_or_else(|| it.span()),
                                None,
                                None,
                                TypeCheckErrorKind::NotYetImplemented(format!(
                                    "field of reference to something that is not a struct: {}",
                                    self.pretty_ty(inner)
                                )),
                            );
                            (None, self.error_ty())
                        }
                    },
                    TypeData::Struct(s) => {
                        let fields = self.struct_fields(s);
                        if let Some(field) = fields.iter().find(|f| f.name.deref() == field.deref())
                        {
                            (
                                Some(field.clone()),
                                self.expect_find_type(&field.ty(self.db, self.root)),
                            )
                        } else {
                            self.push_error(
                                field.span(),
                                None,
                                None,
                                TypeCheckErrorKind::UnknownStructField {
                                    field: field.clone(),
                                    strukt: s.name(self.db),
                                },
                            );
                            (None, self.error_ty())
                        }
                    }
                    TypeData::List(ty) => match field.as_str() {
                        "len" => (
                            Some(Field {
                                parent: FieldParent::List(ty),
                                name: field.clone(),
                                is_ghost: false,
                                ty: None,
                            }),
                            self.int(),
                        ),
                        _ => {
                            return self.expr_error(
                                it.span(),
                                None,
                                None,
                                TypeCheckErrorKind::NotYetImplemented(format!(
                                    "unknown field on list '{field}'"
                                )),
                            )
                        }
                    },
                    _ => {
                        return self.expr_error(
                            it.span(),
                            None,
                            None,
                            TypeCheckErrorKind::NotYetImplemented(format!(
                                "field access with base is '{}'",
                                self.pretty_ty(expr_ty)
                            )),
                        )
                    }
                };

                Expr::new(
                    field_ty.with_ghost(self.is_ghost(expr)).ty(self),
                    ExprData::Field {
                        expr,
                        field_name: field,
                        field: sf,
                    },
                )
            }
            ast::Expr::StructExpr(it) => {
                let name: Ident = if let Some(name) = it.name() {
                    name.into()
                } else {
                    todo!()
                };
                let struct_ty = self.find_named_type(name.clone());

                let s = match self.ty_data(struct_ty) {
                    TypeData::Struct(s) => s,
                    _ => {
                        let expr_err = self.expr_error(
                            name.span(),
                            None,
                            None,
                            TypeCheckErrorKind::UnknownStruct { name },
                        );

                        // NOTE: Still check the types of the fields
                        for f in it.fields() {
                            let _ = self.check(f.span(), f.expr());
                        }

                        return expr_err;
                    }
                };

                let fields = self.struct_fields(s);
                let mut present_fields = vec![];

                for f in it.fields() {
                    let mut matched = false;
                    for sf in &fields {
                        let field_name = Ident::from(f.name().unwrap());
                        if field_name.as_str() == sf.name.as_str() {
                            let value = self.check(f.span(), f.expr());
                            let expected = self.expect_find_type(&sf.ty(self.db, self.root));
                            self.expect_ty(self.expr_span(value), expected, self.expr_ty(value));
                            present_fields.push(StructExprField::new(
                                sf.clone(),
                                field_name,
                                value,
                            ));
                            matched = true;
                        }
                    }
                    if !matched {
                        self.push_error(
                            f.span(),
                            None,
                            None,
                            TypeCheckErrorKind::NotYetImplemented(format!(
                                "field '{}' does not exist on '{}'",
                                f.name().unwrap(),
                                s.name(self.db)
                            )),
                        );
                    }
                }

                Expr {
                    ty: struct_ty,
                    data: ExprData::Struct {
                        struct_declaration: s,
                        struct_span: name.span(),
                        fields: present_fields,
                    },
                }
            }
            ast::Expr::ParenExpr(e) => return self.check(fallback_span, e.expr()),
            ast::Expr::RefExpr(it) => {
                let expr = self.check(it.span(), it.expr());
                let is_mut = it.mut_token().is_some();
                let inner = self.cx.expr_arena[expr].ty;

                let ty = self.ty_id(TypeData::Ref { is_mut, inner });

                Expr::new(ty, ExprData::Ref { is_mut, expr })
            }
            ast::Expr::IdentExpr(it) => {
                let name = if let Some(name) = it.name() {
                    name
                } else {
                    todo!()
                };

                let var = self.lookup_name(&name);
                let ty = self.var_ty(var);

                Expr::new(ty, ExprData::Ident(VariableRef::new(var, name.span())))
            }
            ast::Expr::NullExpr(_) => Expr::new(self.null_ty(), ExprData::Literal(Literal::Null)),
            ast::Expr::ResultExpr(_) => {
                // TODO: Perhaps this should be an error, as commented out below
                // let ty = if let Some(return_ty) = self.return_ty() {
                //     return_ty
                // } else {
                //     self.push_error(
                //         expr.span(),
                //         None,
                //         None,
                //         TypeCheckErrorKind::ResultWithNoReturn,
                //     )
                // };
                let ty = self.return_ty();
                Expr::new(ty, ExprData::Result)
            }
            ast::Expr::QuantifierExpr(it) => {
                let quantifier = match it.quantifier() {
                    Some(q) if q.forall_token().is_some() => Quantifier::Forall,
                    Some(q) if q.exists_token().is_some() => Quantifier::Exists,
                    None => todo!(),
                    _ => todo!(),
                };
                let params = self.check_param_list(it.param_list());

                self.push_scope(|f| f);
                let params = params
                    .into_iter()
                    .map(|param| {
                        let var = self.declare_variable(
                            VariableDeclaration::new_param(param.name.clone()),
                            param.ty,
                            // TODO: Should this not be the ty?
                            param.name.span(),
                        );
                        Param {
                            is_ghost: true,
                            name: var,
                            ty: param.ty,
                        }
                    })
                    .collect();

                let expr = self.check(it.span(), it.expr());
                self.pop_scope();

                Expr::new(
                    self.bool(),
                    ExprData::Quantifier {
                        quantifier,
                        params,
                        expr,
                    },
                )
            }
        };

        self.alloc_expr(new, &expr)
    }

    fn ty_data(&self, ty: TypeId) -> TypeData {
        self.ty_table.lock().unwrap().probe_value(ty)
    }
    pub(crate) fn pretty_ty(&self, ty: TypeId) -> String {
        hir::pretty::ty(self, self.db, ty)
    }
    pub fn expect_ty(
        &mut self,
        span: SourceSpan,
        expected: impl Typed,
        actual: impl Typed,
    ) -> TypeId {
        let expected = expected.ty(self);
        let actual = actual.ty(self);
        match self.unify_inner(expected, actual) {
            Some(x) => x,
            None => self.push_error(
                span,
                None,
                None,
                TypeCheckErrorKind::Mismatch {
                    expected: self.pretty_ty(expected),
                    actual: self.pretty_ty(actual),
                },
            ),
        }
    }
    fn unify(&mut self, span: SourceSpan, t1: impl Typed, t2: impl Typed) -> TypeId {
        let t1 = t1.ty(self);
        let t2 = t2.ty(self);
        match self.unify_inner(t1, t2) {
            Some(x) => x,
            None => self.push_error(
                span,
                None,
                None,
                TypeCheckErrorKind::CantUnify(self.pretty_ty(t1), self.pretty_ty(t2)),
            ),
        }
    }
    fn unify_inner(&mut self, expected: impl Typed, actual: impl Typed) -> Option<TypeId> {
        let expected = expected.ty(self);
        let actual = actual.ty(self);
        Some(match (self.ty_data(expected), self.ty_data(actual)) {
            (TypeData::Error, _) | (_, TypeData::Error) => expected,
            (TypeData::Void, TypeData::Void) => expected,
            (
                TypeData::Ref {
                    is_mut: mut1,
                    inner: inner1,
                },
                TypeData::Ref {
                    is_mut: mut2,
                    inner: inner2,
                },
            ) => {
                let inner = self.unify_inner(inner1, inner2)?;
                self.ty_id(TypeData::Ref {
                    is_mut: mut1 && mut2,
                    inner,
                })
            }
            (TypeData::Optional(inner1), TypeData::Optional(inner2)) => {
                self.unify_inner(inner1, inner2)?;
                expected
            }
            (TypeData::Optional(inner), TypeData::Struct(_)) if inner == actual => expected,
            (TypeData::Struct(_), TypeData::Optional(inner)) if inner == expected => actual,
            (TypeData::Primitive(p1), TypeData::Primitive(p2)) if p1 == p2 => expected,
            (TypeData::Struct(s1), TypeData::Struct(s2)) if s1 == s2 => expected,
            (TypeData::List(s1), TypeData::List(s2)) => {
                self.unify_inner(s1, s2)?;
                expected
            }
            (TypeData::Null, TypeData::Null) => expected,
            (TypeData::Null, TypeData::Optional(_)) => actual,
            (TypeData::Optional(_), TypeData::Null) => expected,

            // Ghost
            (TypeData::Ghost(t1), TypeData::Ghost(t2)) => {
                if let Some(t) = self.unify_inner(t1, t2) {
                    t.ghost().ty(self)
                } else {
                    return None;
                }
            }
            (TypeData::Ghost(t1), _) => {
                if let Some(t) = self.unify_inner(t1, actual) {
                    t.ghost().ty(self)
                } else {
                    return None;
                }
            }
            (TypeData::Free, _) | (_, TypeData::Free) => {
                self.ty_table
                    .lock()
                    .unwrap()
                    .unify_var_var(expected, actual)
                    .unwrap();
                expected
            }
            _ => return None,
        })
    }
    fn push_error(
        &self,
        span: SourceSpan,
        label: Option<String>,
        help: Option<String>,
        kind: TypeCheckErrorKind,
    ) -> TypeId {
        let err = TypeCheckError {
            input: self.program.parse(self.db).tree().to_string(),
            span,
            label,
            help,
            kind,
        };
        TypeCheckErrors::push(self.db, err);
        // eprintln!("{:?}", miette::Error::new(err));
        self.error_ty()
    }
    fn expr_error(
        &mut self,
        expr_or_span: impl Into<SpanOrAstPtr<ast::Expr>>,
        label: Option<String>,
        help: Option<String>,
        kind: TypeCheckErrorKind,
    ) -> ExprIdx {
        let expr_or_span = expr_or_span.into();
        let span = expr_or_span.span();

        self.push_error(span, label, help, kind);

        self.alloc_expr(Expr::new(self.error_ty(), ExprData::Missing), expr_or_span)
    }
    fn alloc_expr(&mut self, expr: Expr, ptr: impl Into<SpanOrAstPtr<ast::Expr>>) -> ExprIdx {
        let ptr = ptr.into();
        let idx = self.cx.expr_arena.alloc(expr);
        self.source_map.expr_map_back.insert(idx, ptr.clone());
        self.source_map.expr_map.insert(ptr, idx);
        idx
    }
    pub fn check_boolean_exprs(
        &mut self,
        exprs: impl Iterator<Item = ast::CommaExpr>,
    ) -> Vec<ExprIdx> {
        let bool_ty = self.bool().ghost();
        exprs
            .map(|comma_expr| {
                let expr = self.check(comma_expr.span(), comma_expr.expr());
                self.expect_ty(comma_expr.span(), bool_ty, self.expr_ty(expr));
                expr
            })
            .collect()
    }
    fn check_assertion(
        &mut self,
        span: SourceSpan,
        kind: AssertionKind,
        exprs: impl Iterator<Item = ast::CommaExpr>,
    ) -> Statement {
        Statement::new(
            span,
            StatementData::Assertion {
                kind,
                exprs: self.check_boolean_exprs(exprs),
            },
        )
    }
    fn check_param_list(&mut self, param_list: Option<ast::ParamList>) -> Vec<Param<Ident>> {
        param_list
            .into_iter()
            .flat_map(|pl| pl.params())
            .map(|p| Param {
                is_ghost: p.is_ghost(),
                name: if let Some(name) = p.name() {
                    name.into()
                } else {
                    todo!()
                },
                ty: if let Some(ty) = p.ty() {
                    self.find_type_src(&ty)
                } else {
                    self.unsourced_ty(self.error_ty())
                }
                .with_ghost(p.is_ghost())
                .ts(self),
            })
            .collect()
    }
    pub(super) fn find_type_src(&mut self, ast_ty: &ast::Type) -> TypeSrcId {
        let (td, ty) = match ast_ty {
            mist_syntax::ast::Type::NamedType(name) => {
                let name = name.name().unwrap().into();
                let ty = self.find_named_type(name);
                let td = match self.ty_data(ty) {
                    TypeData::Struct(s) => TypeData::Struct(s),
                    TypeData::Error => TypeData::Error,
                    _ => todo!(),
                };
                (td, ty)
            }
            mist_syntax::ast::Type::Primitive(it) => match () {
                _ if it.int_token().is_some() => (TypeData::Primitive(Primitive::Int), self.int()),
                _ if it.bool_token().is_some() => {
                    (TypeData::Primitive(Primitive::Bool), self.bool())
                }
                _ => {
                    todo!();
                    // TypeData::Error
                }
            },
            mist_syntax::ast::Type::Optional(it) => {
                let inner = if let Some(ty) = it.ty() {
                    self.find_type_src(&ty)
                } else {
                    todo!()
                };
                let td = TypeData::Optional(inner);
                let ty = td.canonical(&self.cx);
                let ty = self.ty_id(ty);
                (td, ty)
            }
            mist_syntax::ast::Type::RefType(r) => {
                let is_mut = r.mut_token().is_some();

                let inner = if let Some(ty) = r.ty() {
                    self.find_type_src(&ty)
                } else {
                    todo!()
                    // let err = TypeCheckError {
                    //     input: program.program(db).to_string(),
                    //     span: r.span(),
                    //     label: None,
                    //     help: None,
                    //     kind: TypeCheckErrorKind::UndefinedType("what is this".to_string()),
                    // };
                    // eprintln!("{:?}", miette::Error::new(err));

                    // TypeData::Ref {
                    //     is_mut,
                    //     inner: Type::error(db),
                    // }
                };
                let td = TypeData::Ref { is_mut, inner };
                let ty = td.canonical(&self.cx);
                let ty = self.ty_id(ty);
                (td, ty)
            }
            mist_syntax::ast::Type::ListType(t) => {
                let inner = if let Some(ty) = t.ty() {
                    self.find_type_src(&ty)
                } else {
                    todo!()
                    // let err = TypeCheckError {
                    //     input: program.program(db).to_string(),
                    //     span: t.span(),
                    //     label: None,
                    //     help: None,
                    //     kind: TypeCheckErrorKind::UndefinedType("list of what".to_string()),
                    // };
                    // eprintln!("{:?}", miette::Error::new(err));
                    // return Type::error(db);
                };
                let td = TypeData::List(inner);
                let ty = td.canonical(&self.cx);
                let ty = self.ty_id(ty);
                (td, ty)
            }
            mist_syntax::ast::Type::GhostType(t) => {
                let inner = if let Some(ty) = t.ty() {
                    self.find_type_src(&ty)
                } else {
                    todo!()
                    // let err = TypeCheckError {
                    //     input: program.program(db).to_string(),
                    //     span: t.span(),
                    //     label: None,
                    //     help: None,
                    //     kind: TypeCheckErrorKind::UndefinedType("ghost of what".to_string()),
                    // };
                    // eprintln!("{:?}", miette::Error::new(err));
                    // return Type::error(db);
                };
                let td = TypeData::Ghost(inner);
                let ty = td.canonical(&self.cx);
                let ty = self.ty_id(ty);
                (td, ty)
            }
        };

        let ts = TypeSrc { data: Some(td), ty };
        self.alloc_type_src(ts, ast_ty)
    }
    fn check_decreases(&mut self, decreases: Option<ast::Decreases>) -> Decreases {
        if let Some(d) = decreases {
            if d.underscore_token().is_some() {
                Decreases::Inferred
            } else {
                Decreases::Expr(self.check(d.span(), d.expr()))
            }
        } else {
            Decreases::Unspecified
        }
    }
    pub fn check_block(
        &mut self,
        block: &ast::BlockExpr,
        f: impl FnOnce(ScopeFlags) -> ScopeFlags,
    ) -> Block {
        self.push_scope(f);
        let stmts = block
            .statements()
            .map(|stmt| match stmt {
                ast::Stmt::LetStmt(it) => {
                    let span = it.span();
                    let name = it.name().unwrap();
                    let explicit_ty = it.ty().map(|ty| self.find_type_src(&ty));
                    let initializer = self.check(it.span(), it.initializer());

                    let ty = if let Some(ty) = explicit_ty {
                        let ty = self.cx[ty].ty;
                        let span = it
                            .initializer()
                            .map(|i| i.span())
                            .unwrap_or_else(|| it.span());
                        self.expect_ty(span, ty, self.expr_ty(initializer));
                        ty
                    } else {
                        self.expr_ty(initializer)
                    }
                    .with_ghost(self.scope.is_ghost())
                    .ty(self);

                    let var_span = name.span();
                    let var_ty = explicit_ty
                        .unwrap_or_else(|| self.cx.ty_src_arena.alloc(TypeSrc { data: None, ty }));
                    let variable = VariableRef::new(
                        self.declare_variable(
                            VariableDeclaration::new_let(name),
                            var_ty,
                            match it.ty() {
                                Some(ty) => SpanOrAstPtr::from(&ty),
                                None => SpanOrAstPtr::from(var_span),
                            },
                        ),
                        var_span,
                    );

                    Statement::new(
                        span,
                        StatementData::Let {
                            variable,
                            explicit_ty,
                            initializer,
                        },
                    )
                }
                ast::Stmt::Item(it) => Statement::new(
                    it.span(),
                    StatementData::Expr(self.expr_error(
                        it.span(),
                        None,
                        None,
                        TypeCheckErrorKind::NotYetImplemented(
                            "items in statement position".to_string(),
                        ),
                    )),
                ),
                ast::Stmt::ExprStmt(it) => Statement::new(
                    it.span(),
                    StatementData::Expr(self.check(it.span(), it.expr())),
                ),
                ast::Stmt::AssertStmt(it) => {
                    self.check_assertion(it.span(), AssertionKind::Assert, it.comma_exprs())
                }
                ast::Stmt::AssumeStmt(it) => {
                    self.check_assertion(it.span(), AssertionKind::Assume, it.comma_exprs())
                }
                ast::Stmt::WhileStmt(it) => Statement::new(
                    it.span(),
                    StatementData::While {
                        expr: self.check(it.span(), it.expr()),
                        invariants: it
                            .invariants()
                            .map(|inv| self.check_boolean_exprs(inv.comma_exprs()))
                            .collect(),
                        decreases: self.check_decreases(it.decreases()),
                        body: self.check_block(&it.block_expr().unwrap(), id),
                    },
                ),
            })
            .collect();
        let (tail_expr, return_ty) = if let Some(tail_expr) = block.tail_expr() {
            let tail_expr = self.check(tail_expr.span(), Some(tail_expr));
            (
                Some(tail_expr),
                self.expr_ty(tail_expr).with_ghost(self.scope.is_ghost()),
            )
        } else {
            (None, self.void().with_ghost(self.scope.is_ghost()))
        };
        self.pop_scope();
        Block {
            stmts,
            tail_expr,
            return_ty: return_ty.ty(self),
        }
    }
    pub fn alloc_type_src(
        &mut self,
        ts: TypeSrc,
        ty_src: impl Into<SpanOrAstPtr<ast::Type>>,
    ) -> TypeSrcId {
        let id = self.cx.ty_src_arena.alloc(ts);
        let span = ty_src.into();
        self.source_map.ty_src_map.insert(id, span.clone());
        self.source_map.ty_src_map_back.insert(span, id);
        id
    }
    pub fn declare_variable(
        &mut self,
        decl: VariableDeclaration,
        ty: TypeSrcId,
        ty_span: impl Into<SpanOrAstPtr<ast::Type>>,
    ) -> VariableIdx {
        let name = decl.name.to_string();
        let var = self.cx.declarations.alloc(
            decl,
            Variable::new(self.db, VariableId::new(self.db, name.clone())),
        );
        self.scope.insert(name, var);
        self.cx.var_types.insert(var, ty);
        let ty_src = ty_span.into();
        self.source_map.ty_src_map.insert(ty, ty_src.clone());
        self.source_map.ty_src_map_back.insert(ty_src, ty);
        var
    }
    pub fn var_ty(&self, var: VariableIdx) -> TypeId {
        self.cx[*self
            .cx
            .var_types
            .get(var)
            .expect("VariableIdx was not in types map")]
        .ty
    }
    pub fn lookup_name(&mut self, name: &ast::Name) -> VariableIdx {
        if let Some(var) = self.scope.get(&name.to_string()) {
            var
        } else {
            let err_ty = self.push_error(
                name.span(),
                None,
                None,
                TypeCheckErrorKind::UndefinedVariable(name.to_string()),
            );
            let ty = self.unsourced_ty(err_ty);
            self.declare_variable(
                VariableDeclaration::new_undefined(name.clone()),
                ty,
                name.span(),
            )
        }
    }

    fn find_named_type(&self, name: Ident) -> TypeId {
        self.cx
            .named_types
            .get(&name.to_string())
            .copied()
            .unwrap_or_else(|| {
                self.push_error(
                    name.span(),
                    None,
                    None,
                    TypeCheckErrorKind::UndefinedType(name.to_string()),
                )
            })
    }

    fn struct_fields(&self, s: crate::hir::Struct) -> Vec<Field> {
        crate::hir::struct_fields(self.db, s)
    }

    fn is_ghost(&mut self, e: ExprIdx) -> bool {
        self.expr_ty(e).tc_is_ghost(self)
    }

    pub(super) fn unsourced_ty(&mut self, ty: impl Typed) -> TypeSrcId {
        let ty = ty.ty(self);
        self.cx.ty_src_arena.alloc(TypeSrc { data: None, ty })
    }

    pub(super) fn ghostify(&mut self, ts: TypeSrcId, is_ghost: bool) -> TypeSrcId {
        let ty = self.cx[ts].ty;
        if is_ghost && !ty.tc_is_ghost(self) {
            self.unsourced_ty(ty.ghost())
        } else {
            ts
        }
    }

    fn return_ty(&self) -> TypeId {
        self.return_ty
            .map(|ty| self.cx[ty].ty)
            .unwrap_or_else(|| self.void())
    }

    pub(super) fn expect_find_type(&mut self, ty: &Option<ast::Type>) -> TypeId {
        match ty {
            Some(ty) => {
                let ts = self.find_type_src(ty);
                self.cx[ts].ty
            }
            None => self.error_ty(),
        }
    }
    pub(super) fn expect_find_type_src(&mut self, ty: &Option<ast::Type>) -> TypeSrcId {
        match ty {
            Some(ty) => self.find_type_src(ty),
            None => self.unsourced_ty(self.error_ty()),
        }
    }

    fn new_free(&mut self) -> TypeId {
        let key = self.ty_table.lock().unwrap().new_key(TypeData::Free);
        self.ty_keys.push(key);
        key
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ghosted<T>(pub T, pub bool);
impl Ghosted<TypeSrcId> {
    pub fn ts(&self, tc: &mut TypeChecker) -> TypeSrcId {
        if self.1 {
            tc.ghostify(self.0, self.1)
        } else {
            self.0
        }
    }
}
pub trait Typed {
    fn with_ghost(self, ghost: bool) -> Ghosted<Self>
    where
        Self: Sized,
    {
        Ghosted(self, ghost)
    }
    fn ty(&self, tc: &mut TypeChecker) -> TypeId;
}

impl Typed for TypeId {
    fn ty(&self, _tc: &mut TypeChecker) -> TypeId {
        *self
    }
}
impl Typed for TypeSrcId {
    fn ty(&self, tc: &mut TypeChecker) -> TypeId {
        tc.cx[*self].ty
    }
}
impl<T: Typed> Typed for Ghosted<T> {
    fn ty(&self, tc: &mut TypeChecker) -> TypeId {
        if self.1 {
            let ty = self.0.ty(tc);
            if ty.tc_is_ghost(tc) {
                ty
            } else {
                tc.ty_id(TypeData::Ghost(ty))
            }
        } else {
            self.0.ty(tc)
        }
    }
}

impl hir::pretty::PrettyPrint for ItemContext {
    fn resolve_var(&self, idx: VariableIdx) -> Ident {
        self.declarations.map[idx].name.clone()
    }

    fn resolve_var_ty(&self, idx: VariableIdx) -> TypeId {
        self.var_ty(idx)
    }

    fn resolve_expr(&self, idx: ExprIdx) -> &Expr {
        &self.expr_arena[idx]
    }

    fn resolve_ty(&self, ty: TypeId) -> TypeData {
        if self.ty_table.contains_idx(ty.0) {
            self.ty_table[ty.0].clone()
        } else {
            error!("tried to get type id which was not in ItemContext: {ty:?}");
            TypeData::Error
        }
    }

    fn resolve_src_ty(&self, ts: TypeSrcId) -> TypeId {
        self.ty_src_arena[ts].ty
    }
}

impl hir::pretty::PrettyPrint for TypeChecker<'_> {
    fn resolve_var(&self, idx: VariableIdx) -> Ident {
        self.cx.declarations.map[idx].name.clone()
    }

    fn resolve_var_ty(&self, idx: VariableIdx) -> TypeId {
        self.var_ty(idx)
    }

    fn resolve_expr(&self, idx: ExprIdx) -> &Expr {
        &self.cx.expr_arena[idx]
    }

    fn resolve_ty(&self, ty: TypeId) -> TypeData {
        self.ty_table.lock().unwrap().probe_value(ty)
    }

    fn resolve_src_ty(&self, ts: TypeSrcId) -> TypeId {
        self.cx.ty_src_arena[ts].ty
    }
}

impl ItemContext {
    pub fn pretty_expr(&self, db: &dyn crate::Db, expr: ExprIdx) -> String {
        hir::pretty::expr(self, db, expr)
    }
    pub fn pretty_ty(&self, db: &dyn crate::Db, ty: TypeId) -> String {
        hir::pretty::ty(self, db, ty)
    }
}

#[salsa::accumulator]
pub struct TypeCheckErrors(TypeCheckError);

#[derive(Debug, Diagnostic, Clone, Eq, PartialEq, Error)]
#[error("{kind}")]
pub struct TypeCheckError {
    #[source_code]
    pub input: String,
    #[label("{}", label.as_deref().unwrap_or("here"))]
    pub span: SourceSpan,
    pub label: Option<String>,
    #[help]
    pub help: Option<String>,
    pub kind: TypeCheckErrorKind,
}

#[derive(Debug, Diagnostic, Clone, Eq, PartialEq, Error)]
pub enum TypeCheckErrorKind {
    #[error("type `{0}` was not found")]
    UndefinedType(String),
    #[error("variable `{0}` was not found in this scope")]
    UndefinedVariable(String),
    #[error("missing initializer")]
    MissingInitializer,
    #[error("can't unify `{0}` with `{1}`")]
    CantUnify(String, String),
    #[error("missing left-hand-side of binary operation")]
    MissingLhs,
    #[error("missing right-hand-side of binary operation")]
    MissingRhs,
    #[error("missing expression")]
    MissingExpression,
    #[error("`result` used in function that does not have a return type")]
    ResultWithNoReturn,
    #[error("expected type `{expected}`, but found `{actual}`")]
    Mismatch { expected: String, actual: String },
    #[error("returned valued in function that did not return anything")]
    ReturnedValueWithNoReturnValue,
    #[error("the field `{field}` does not exist on struct `{strukt}`")]
    UnknownStructField { field: Ident, strukt: Ident },
    #[error("not yet implemented: {0}")]
    NotYetImplemented(String),
    #[error("no struct with name `{name}` was found")]
    UnknownStruct { name: Ident },
    #[error("`ghost` was used where only non-ghost can be used")]
    GhostUsedInNonGhost,
    #[error("only `ghost` functions can be declared without a body")]
    NonGhostFunctionWithoutBody,
    #[error("functions called in `ghost` functions must be either `ghost`, `pure`, or both")]
    NonGhostNorPureCalledInGhost,
    #[error("tried to assign a `ghost` value to a variable that is not marked `ghost`")]
    GhostAssignedToNonGhost,
}
