use std::{collections::HashMap, ops::Deref};

use bitflags::bitflags;
use derive_new::new;
use la_arena::{Arena, ArenaMap};
use miette::Diagnostic;
use mist_syntax::{
    ast::{
        self,
        operators::{ArithOp, BinaryOp, CmpOp},
        HasAttrs, HasName, Spanned,
    },
    ptr::AstPtr,
    SourceSpan,
};
use thiserror::Error;

use crate::hir::{
    self, AssertionKind, Block, Condition, Decreases, Else, Expr, ExprData, ExprIdx, Field,
    FieldParent, Ident, IfExpr, Literal, Param, ParamList, Primitive, Program, Quantifier,
    Statement, StatementData, StructExprField, Type, TypeData, Variable, VariableId, VariableIdx,
    VariableRef,
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

    pub fn kind(&self) -> VariableDeclarationKind {
        self.kind
    }
}

impl Spanned for &'_ VariableDeclaration {
    fn span(self) -> SourceSpan {
        self.name.span()
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct ItemContext {
    function_context: Option<FunctionContext>,
    declarations: Trace<Variable, VariableDeclaration>,
    types: ArenaMap<VariableIdx, Type>,
    expr_arena: Arena<Expr>,

    params: ParamList<VariableIdx>,
    body_expr: Option<ExprIdx>,
}

impl std::ops::Index<ExprIdx> for ItemContext {
    type Output = Expr;

    fn index(&self, index: ExprIdx) -> &Self::Output {
        &self.expr_arena[index]
    }
}
impl std::ops::Index<VariableIdx> for ItemContext {
    type Output = Variable;

    fn index(&self, index: VariableIdx) -> &Self::Output {
        &self.declarations.arena[index]
    }
}
impl ItemContext {
    pub fn function_context(&self) -> Option<&FunctionContext> {
        self.function_context.as_ref()
    }
    pub fn function_var(&self) -> Option<VariableRef> {
        self.function_context.as_ref().map(|cx| cx.function_var)
    }
    pub fn conditions(&self) -> impl Iterator<Item = &Condition> {
        self.function_context.iter().flat_map(|cx| &cx.conditions)
    }
    pub fn params(&self) -> &ParamList<VariableIdx> {
        &self.params
    }
    pub fn body_expr(&self) -> Option<ExprIdx> {
        self.body_expr
    }
    pub fn var_ty(&self, var: impl Into<VariableIdx>) -> Type {
        self.types[var.into()]
    }
    pub fn expr(&self, expr: ExprIdx) -> &Expr {
        &self.expr_arena[expr]
    }
    pub fn var(&self, var: impl Into<VariableIdx>) -> Variable {
        self.declarations.arena[var.into()]
    }
    pub fn decl(&self, var: impl Into<VariableIdx>) -> &VariableDeclaration {
        &self.declarations.map[var.into()]
    }
    pub fn var_span(&self, var: impl Into<VariableIdx>) -> SourceSpan {
        self.declarations.map[var.into()].span()
    }
    pub fn var_ident(&self, var: impl Into<VariableIdx>) -> &Ident {
        &self.declarations.map[var.into()].name
    }
}

impl Type {
    pub fn error(db: &dyn crate::Db) -> Self {
        Type::new(db, TypeData::Error, None)
    }
    pub fn void(db: &dyn crate::Db) -> Self {
        Type::new(db, TypeData::Void, None)
    }
    pub fn primitive(db: &dyn crate::Db, primitive: Primitive) -> Self {
        Type::new(db, TypeData::Primitive(primitive), None)
    }
    pub fn int(db: &dyn crate::Db) -> Self {
        Self::primitive(db, Primitive::Int)
    }
    pub fn bool(db: &dyn crate::Db) -> Self {
        Self::primitive(db, Primitive::Bool)
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionContext {
    function_var: VariableRef,
    conditions: Vec<Condition>,
    decreases: Decreases,
}

impl FunctionContext {
    pub fn function_var(&self) -> VariableRef {
        self.function_var
    }
    pub fn conditions(&self) -> &[Condition] {
        self.conditions.as_ref()
    }
    pub fn decreases(&self) -> Decreases {
        self.decreases
    }
}

type ExprPtr = AstPtr<ast::Expr>;
type ExprSrc = ExprOrSpan;

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ItemSourceMap {
    expr_map: HashMap<ExprSrc, ExprIdx>,
    expr_map_back: HashMap<ExprIdx, ExprSrc>,
}

impl ItemSourceMap {
    pub fn expr_span(&self, expr: ExprIdx) -> SourceSpan {
        self.expr_map_back[&expr].span()
    }
}

pub struct TypeCheckExpr<'w> {
    db: &'w dyn crate::Db,
    program: Program,
    return_ty: Option<Type>,
    scope: Scope,
    scope_stack: Vec<Scope>,
    source_map: ItemSourceMap,
    item: ItemContext,
}

impl From<TypeCheckExpr<'_>> for (ItemContext, ItemSourceMap) {
    fn from(value: TypeCheckExpr<'_>) -> Self {
        (value.item, value.source_map)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Trace<T, V> {
    arena: Arena<T>,
    map: ArenaMap<la_arena::Idx<T>, V>,
}

impl<T, V> Trace<T, V> {
    pub fn new() -> Self {
        Trace {
            arena: Default::default(),
            map: Default::default(),
        }
    }

    pub fn alloc(&mut self, value: V, data: T) -> la_arena::Idx<T> {
        let id = self.arena.alloc(data);
        self.map.insert(id, value);
        id
    }
}
impl<T, V> Default for Trace<T, V> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, derive_more::From)]
enum ExprOrSpan {
    Expr(ExprPtr),
    Span(SourceSpan),
}

impl ExprOrSpan {
    fn into_expr(self) -> Option<ExprPtr> {
        match self {
            ExprOrSpan::Expr(expr) => Some(expr),
            ExprOrSpan::Span(_) => None,
        }
    }
}
impl Spanned for &'_ ExprOrSpan {
    fn span(self) -> SourceSpan {
        match self {
            ExprOrSpan::Expr(expr) => expr.span(),
            ExprOrSpan::Span(span) => *span,
        }
    }
}
impl From<ast::Expr> for ExprOrSpan {
    fn from(value: ast::Expr) -> Self {
        AstPtr::new(&value).into()
    }
}
impl From<&'_ ast::Expr> for ExprOrSpan {
    fn from(value: &ast::Expr) -> Self {
        AstPtr::new(value).into()
    }
}

impl<'a> TypeCheckExpr<'a> {
    pub(crate) fn init(
        db: &'a dyn crate::Db,
        program: Program,
        function: Option<hir::Function>,
    ) -> Self {
        let mut checker = Self {
            db,
            program,
            return_ty: function.and_then(|f| f.ret(db)),
            scope: Default::default(),
            scope_stack: vec![],
            source_map: Default::default(),
            item: Default::default(),
        };

        let is_ghost = if let Some(f) = function {
            f.attrs(db).is_ghost()
        } else {
            false
        };

        if is_ghost {
            checker = checker.ghosted();
        }

        for item in program.items(db) {
            let f = match hir::item(db, program, item.clone()) {
                Some(hir::Item::Function(f)) => f,
                _ => continue,
            };
            let is_ghost = f.attrs(db).is_ghost();

            let params = ParamList {
                params: f
                    .param_list(db)
                    .params
                    .iter()
                    .map(|param| Param {
                        is_ghost: param.is_ghost,
                        name: param.name.clone(),
                        ty: param.ty.with_ghost(db, is_ghost),
                    })
                    .collect(),
            };
            let return_ty = f
                .ret(db)
                .unwrap_or_else(|| Type::void(db))
                .with_ghost(db, is_ghost);

            let var_span = f.name(db).span();
            let var = checker.declare_variable(
                VariableDeclaration::new_function(f.name(db).clone()),
                Type::new(
                    db,
                    TypeData::Function {
                        attrs: f.attrs(db),
                        name: Some(f.name(db).clone()),
                        params,
                        return_ty,
                    },
                    Some(var_span),
                ),
            );

            if Some(f) == function {
                checker.item.function_context = Some(FunctionContext {
                    function_var: VariableRef::new(var, var_span),
                    decreases: Default::default(),
                    conditions: vec![],
                });
            }
        }

        if let Some(f) = function {
            checker.item.params = f
                .param_list(db)
                .params
                .iter()
                .map(|p| {
                    let var = checker.declare_variable(
                        VariableDeclaration::new_param(p.name.clone()),
                        p.ty.with_ghost(db, is_ghost),
                    );
                    Param {
                        is_ghost: p.is_ghost,
                        name: var,
                        ty: p.ty,
                    }
                })
                .collect();

            let conditions = f
                .syntax(db)
                .conditions()
                .map(|c| match c {
                    ast::Condition::Requires(r) => {
                        Condition::Requires(checker.check_boolean_exprs(r.comma_exprs()))
                    }
                    ast::Condition::Ensures(r) => {
                        Condition::Ensures(checker.check_boolean_exprs(r.comma_exprs()))
                    }
                })
                .collect();

            let decreases = checker.check_decreases(f.syntax(db).decreases());

            if let Some(cx) = &mut checker.item.function_context {
                cx.conditions = conditions;
                cx.decreases = decreases;
            }
        }

        checker
    }

    pub fn set_body_expr_from_block(&mut self, block: Block, node: ast::BlockExpr) {
        let idx = self.alloc_expr(
            Expr::new(block.return_ty, ExprData::Block(block)),
            ast::Expr::from(node),
        );
        self.item.body_expr = Some(idx);
    }
    pub fn set_body_expr(&mut self, body_expr: ExprIdx) {
        self.item.body_expr = Some(body_expr);
    }

    pub fn ghosted(mut self) -> Self {
        debug_assert!(
            self.scope_stack.is_empty(),
            "Tried to make a checker ghost, while it was in operation"
        );
        if let Some(ty) = self.return_ty {
            self.return_ty = Some(ty.ghost(self.db));
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
    fn check_if_expr(&mut self, if_expr: ast::IfExpr) -> IfExpr {
        let condition = self.check(if_expr.span(), if_expr.condition());

        let condition_ty = self.expr_ty(condition);
        let is_ghost = condition_ty.is_ghost(self.db);
        if is_ghost {
            self.expect_ty(
                if_expr
                    .condition()
                    .map(|e| e.span())
                    .unwrap_or_else(|| if_expr.span()),
                Type::bool(self.db).ghost(self.db),
                condition_ty,
            );
        } else {
            self.expect_ty(
                if_expr
                    .condition()
                    .map(|e| e.span())
                    .unwrap_or_else(|| if_expr.span()),
                Type::bool(self.db),
                condition_ty,
            );
        }

        let then_branch = if let Some(then_branch) = if_expr.then_branch() {
            self.check_block(&then_branch, |f| {
                if is_ghost {
                    f | ScopeFlags::GHOST
                } else {
                    f
                }
            })
        } else {
            todo!()
        };
        let else_branch =
            if_expr.else_branch().map(|else_branch| match else_branch {
                ast::IfExprElse::IfExpr(e) => Else::If(self.check_if_expr(e)),
                ast::IfExprElse::BlockExpr(b) => Else::Block(self.check_block(&b, |f| {
                    if is_ghost {
                        f | ScopeFlags::GHOST
                    } else {
                        f
                    }
                })),
            });

        let ty = if let Some(b) = &else_branch {
            let first_block = b.first_block();
            let span = match (first_block.tail_expr, first_block.stmts.last()) {
                (Some(tail_expr), _) => self.expr_span(tail_expr),
                (None, Some(last_stmt)) => last_stmt.span,
                (None, None) => if_expr.span(),
            };
            self.unify(
                span,
                then_branch.return_ty.with_ghost(self.db, is_ghost),
                b.return_ty(self.db),
            )
        } else {
            self.expect_ty(
                if_expr.span(),
                Type::void(self.db).with_ghost(self.db, is_ghost),
                then_branch.return_ty,
            )
        };

        IfExpr {
            if_span: if_expr.if_token().unwrap().span(),
            is_ghost,
            return_ty: ty,
            condition,
            then_branch,
            else_branch: else_branch.map(Box::new),
        }
    }
    pub fn expr_ty(&self, expr: ExprIdx) -> Type {
        self.item.expr_arena[expr].ty
    }
    pub fn expr_span(&self, expr: ExprIdx) -> SourceSpan {
        self.source_map.expr_map_back[&expr].span()
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
                    Type::int(self.db).with_ghost(self.db, self.scope.is_ghost()),
                    ExprData::Literal(Literal::Int(s.to_string().parse().unwrap())),
                ),
                ast::LiteralKind::Bool(b) => Expr::new(
                    Type::bool(self.db).with_ghost(self.db, self.scope.is_ghost()),
                    ExprData::Literal(Literal::Bool(b)),
                ),
            },
            ast::Expr::IfExpr(it) => {
                let if_expr = self.check_if_expr(it.clone());
                Expr::new(if_expr.return_ty, ExprData::If(if_expr))
            }
            ast::Expr::WhileExpr(_) => todo!(),
            ast::Expr::PrefixExpr(it) => {
                let (op_token, op) = if let Some(op) = it.op_details() {
                    op
                } else {
                    todo!("{it:#?}")
                };
                let inner = self.check(it.span(), it.expr());
                let inner_span = self.expr_span(inner);
                let inner_ty = self.expr_ty(inner);

                let is_ghost = self.is_ghost(inner);

                let ty: Type = match op {
                    ast::operators::UnaryOp::Not => {
                        self.expect_ty(inner_span, Type::bool(self.db), inner_ty);
                        Type::bool(self.db)
                    }
                    ast::operators::UnaryOp::Neg => {
                        self.expect_ty(inner_span, Type::int(self.db), inner_ty);
                        Type::int(self.db)
                    }
                };

                let ty = if is_ghost { ty.ghost(self.db) } else { ty };

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

                    let return_ty = self.return_ty.unwrap_or_else(|| Type::void(self.db));
                    self.expect_ty(expr_span, return_ty, self.expr_ty(expr_idx));

                    // TODO: These properly should not be Error
                    Expr::new(Type::error(self.db), ExprData::Return(Some(expr_idx)))
                } else {
                    Expr::new(Type::error(self.db), ExprData::Return(None))
                }
            }
            ast::Expr::BinExpr(it) => {
                let lhs = self.check(it.span(), it.lhs());
                let (op_token, op) = if let Some(op) = it.op_details() {
                    op
                } else {
                    todo!()
                };
                let rhs = self.check(it.span(), it.rhs());

                let lhs_ty = self.expr_ty(lhs).strip_ghost(self.db);
                let rhs_ty = self.expr_ty(rhs).strip_ghost(self.db);

                let is_ghost = self.is_ghost(lhs) || self.is_ghost(rhs);
                let int_ty = Type::int(self.db);
                let bool_ty = Type::bool(self.db);

                let ty = match op {
                    BinaryOp::LogicOp(_) => {
                        self.expect_ty(it.span(), bool_ty, lhs_ty);
                        self.expect_ty(it.span(), bool_ty, rhs_ty);
                        bool_ty
                    }
                    BinaryOp::CmpOp(CmpOp::Eq { .. }) => {
                        self.unify(it.span(), lhs_ty, rhs_ty);
                        Type::bool(self.db)
                    }
                    BinaryOp::CmpOp(CmpOp::Ord { .. }) => {
                        self.expect_ty(it.span(), int_ty, lhs_ty);
                        self.expect_ty(it.span(), int_ty, rhs_ty);
                        Type::bool(self.db)
                    }
                    BinaryOp::ArithOp(op) => match op {
                        ArithOp::Add => match lhs_ty.data(self.db) {
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
                            Type::new(
                                self.db,
                                TypeData::Primitive(Primitive::Int),
                                Some(expr.span()),
                            )
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

                let ty = if is_ghost { ty.ghost(self.db) } else { ty };

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

                match self.item.expr_arena[fn_expr].ty.data(self.db) {
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
                                    .map(ExprOrSpan::from)
                                    .unwrap_or_else(|| it.span().into()),
                                None,
                                None,
                                TypeCheckErrorKind::NotYetImplemented(
                                    "argument count mismatch".to_string(),
                                ),
                            );
                        }
                        for (a, b) in args.iter().zip(params.iter().map(|p| p.ty)) {
                            self.expect_ty(
                                self.expr_span(*a),
                                b.with_ghost(self.db, ghostify_pure),
                                self.item.expr_arena[*a].ty,
                            );
                        }

                        Expr {
                            ty: return_ty.with_ghost(self.db, ghostify_pure),
                            data: ExprData::Call {
                                expr: fn_expr,
                                args,
                            },
                        }
                    }
                    TypeData::Error => Expr {
                        ty: Type::error(self.db),
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
                            expr,
                            None,
                            None,
                            TypeCheckErrorKind::NotYetImplemented("inference of '..'".to_string()),
                        )
                    }
                    (None, Some(x)) | (Some(x), None) => {
                        let x_ty = self.expr_ty(x);
                        self.expect_ty(
                            self.expr_span(x),
                            Type::int(self.db),
                            x_ty.strip_ghost(self.db),
                        );
                        x_ty
                    }
                    (Some(lhs), Some(rhs)) => {
                        let lhs_ty = self.expr_ty(lhs);
                        let rhs_ty = self.expr_ty(rhs);
                        self.expect_ty(
                            self.expr_span(lhs),
                            Type::int(self.db),
                            lhs_ty.strip_ghost(self.db),
                        );
                        self.expect_ty(
                            self.expr_span(rhs),
                            Type::int(self.db),
                            rhs_ty.strip_ghost(self.db),
                        );
                        lhs_ty
                    }
                };

                Expr::new(
                    Type::new(self.db, TypeData::Range(ty), None),
                    ExprData::Range { lhs, rhs },
                )
            }
            ast::Expr::IndexExpr(it) => {
                let base = self.check(it.span(), it.base());
                let index = self.check(it.span(), it.index());

                let base_ty = self.expr_ty(base);
                let index_ty = self.expr_ty(index);

                let is_ghost = base_ty.is_ghost(self.db) || index_ty.is_ghost(self.db);

                let is_range = match index_ty.data(self.db) {
                    TypeData::Primitive(Primitive::Int) => false,
                    TypeData::Range(idx) => {
                        self.expect_ty(it.span(), Type::int(self.db).ghost(self.db), *idx);
                        true
                    }
                    _ => {
                        self.expect_ty(it.span(), Type::int(self.db).ghost(self.db), index_ty);
                        false
                    }
                };

                match base_ty.strip_ghost(self.db).data(self.db) {
                    TypeData::List(elem_ty) => {
                        if is_range {
                            Expr::new(
                                base_ty.with_ghost(self.db, is_ghost),
                                ExprData::Index { base, index },
                            )
                        } else {
                            Expr::new(
                                elem_ty.with_ghost(self.db, is_ghost),
                                ExprData::Index { base, index },
                            )
                        }
                    }
                    _ => {
                        return self.expr_error(
                            expr,
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
                        // self.expect_ty(comma_expr.span(), bool_ty, self.expr_ty(expr));
                        expr
                    })
                    .collect();

                if let Some(ty) = elem_ty {
                    Expr::new(
                        Type::new(self.db, TypeData::List(ty.strip_ghost(self.db)), None)
                            .with_ghost(self.db, ty.is_ghost(self.db)),
                        ExprData::List { elems },
                    )
                } else {
                    return self.expr_error(
                        it.span(),
                        None,
                        None,
                        TypeCheckErrorKind::NotYetImplemented(
                            "type inference of empty lists".to_string(),
                        ),
                    );
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
                let sf: Option<Field> = match expr_ty.strip_ghost(self.db).data(self.db) {
                    TypeData::Error => None,
                    TypeData::Ref { is_mut, inner } => match inner.data(self.db) {
                        &TypeData::Struct(s) => {
                            let fields = self.struct_fields(s);
                            if let Some(field) =
                                fields.iter().find(|f| f.name.as_str() == field.as_str())
                            {
                                Some(field.clone())
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
                                    "reference to something that is not a struct: {}",
                                    self.pretty_ty(*inner)
                                )),
                            );
                            None
                        }
                    },
                    TypeData::Struct(s) => {
                        let fields = self.struct_fields(*s);
                        if let Some(field) = fields.iter().find(|f| f.name.deref() == field.deref())
                        {
                            Some(field.clone())
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
                            None
                        }
                    }
                    TypeData::List(ty) => match field.as_str() {
                        "len" => Some(Field {
                            parent: FieldParent::List(*ty),
                            name: field.clone(),
                            is_ghost: false,
                            ty: Type::int(self.db),
                        }),
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
                    sf.as_ref()
                        .map(|f| f.ty)
                        .unwrap_or_else(|| Type::error(self.db))
                        .with_ghost(self.db, self.is_ghost(expr)),
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

                let s = match struct_ty.data(self.db) {
                    TypeData::Struct(s) => *s,
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
                            self.expect_ty(self.expr_span(value), sf.ty, self.expr_ty(value));
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
                let span = expr.span();
                let expr = self.check(it.span(), it.expr());
                let is_mut = it.mut_token().is_some();
                let inner = self.item.expr_arena[expr].ty;

                let ty = Type::new(self.db, TypeData::Ref { is_mut, inner }, Some(span));

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
            ast::Expr::NullExpr(_) => Expr::new(
                Type::new(self.db, TypeData::Null, Some(expr.span())),
                ExprData::Literal(Literal::Null),
            ),
            ast::Expr::ResultExpr(_) => {
                let ty = if let Some(return_ty) = self.return_ty {
                    return_ty
                } else {
                    self.push_error(
                        expr.span(),
                        None,
                        None,
                        TypeCheckErrorKind::ResultWithNoReturn,
                    )
                };
                Expr::new(ty, ExprData::Result)
            }
            ast::Expr::QuantifierExpr(it) => {
                let quantifier = match it.quantifier() {
                    Some(q) if q.forall_token().is_some() => Quantifier::Forall,
                    Some(q) if q.exists_token().is_some() => Quantifier::Exists,
                    None => todo!(),
                    _ => todo!(),
                };
                let params = check_param_list(self.db, self.program, it.param_list());

                self.push_scope(|f| f);
                let params = params
                    .params
                    .iter()
                    .map(|param| {
                        let var = self.declare_variable(
                            VariableDeclaration::new_param(param.name.clone()),
                            param.ty,
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
                    Type::bool(self.db),
                    ExprData::Quantifier {
                        quantifier,
                        params,
                        expr,
                    },
                )
            }
        };

        self.alloc_expr(new, AstPtr::new(&expr))
    }
    pub(crate) fn pretty_ty(&self, ty: Type) -> String {
        hir::pretty::ty(self, self.db, ty)
    }
    pub fn expect_ty(&mut self, span: SourceSpan, expected: Type, actual: Type) -> Type {
        self.unify_inner(expected, actual).unwrap_or_else(|| {
            self.push_error(
                span,
                None,
                None,
                TypeCheckErrorKind::Mismatch {
                    expected: self.pretty_ty(expected),
                    actual: self.pretty_ty(actual),
                },
            )
        })
    }
    fn unify(&mut self, span: SourceSpan, t1: Type, t2: Type) -> Type {
        self.unify_inner(t1, t2).unwrap_or_else(|| {
            self.push_error(
                span,
                None,
                None,
                TypeCheckErrorKind::CantUnify(self.pretty_ty(t1), self.pretty_ty(t2)),
            )
        })
    }
    fn unify_inner(&mut self, expected: Type, actual: Type) -> Option<Type> {
        Some(match (expected.data(self.db), actual.data(self.db)) {
            (TypeData::Error, _) => actual,
            (_, TypeData::Error) => expected,
            (TypeData::Void, TypeData::Void) => expected,
            (
                &TypeData::Ref {
                    is_mut: mut1,
                    inner: inner1,
                },
                &TypeData::Ref {
                    is_mut: mut2,
                    inner: inner2,
                },
            ) => Type::new(
                self.db,
                TypeData::Ref {
                    is_mut: mut1 && mut2,
                    inner: self.unify_inner(inner1, inner2)?,
                },
                // TODO: What is the appropriate span here?
                expected.span(self.db),
            ),
            (TypeData::Optional(inner1), TypeData::Optional(inner2)) if inner1 == inner2 => {
                expected
            }
            (TypeData::Optional(inner), TypeData::Struct(_))
                if inner.without_span(self.db) == actual.without_span(self.db) =>
            {
                expected
            }
            (TypeData::Struct(_), TypeData::Optional(inner))
                if inner.without_span(self.db) == expected.without_span(self.db) =>
            {
                actual
            }
            (TypeData::Primitive(p1), TypeData::Primitive(p2)) if p1 == p2 => expected,
            (TypeData::Struct(s1), TypeData::Struct(s2)) if s1 == s2 => expected,
            (TypeData::List(s1), TypeData::List(s2)) => {
                Type::new(self.db, TypeData::List(self.unify_inner(*s1, *s2)?), None)
            }
            (TypeData::Null, TypeData::Null) => expected,
            (TypeData::Null, TypeData::Optional(_)) => actual,
            (TypeData::Optional(_), TypeData::Null) => expected,

            // Ghost
            (&TypeData::Ghost(t1), &TypeData::Ghost(t2)) => {
                if let Some(t) = self.unify_inner(t1.strip_ghost(self.db), t2.strip_ghost(self.db))
                {
                    t.ghost(self.db)
                } else {
                    return None;
                }
            }
            (&TypeData::Ghost(t1), _) => {
                if let Some(t) = self.unify_inner(t1, actual) {
                    t.ghost(self.db)
                } else {
                    return None;
                }
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
    ) -> Type {
        let err = TypeCheckError {
            input: self.program.program(self.db).to_string(),
            span,
            label,
            help,
            kind,
        };
        TypeCheckErrors::push(self.db, err);
        // eprintln!("{:?}", miette::Error::new(err));
        Type::new(self.db, TypeData::Error, Some(span))
    }
    fn expr_error(
        &mut self,
        expr_or_span: impl Into<ExprOrSpan>,
        label: Option<String>,
        help: Option<String>,
        kind: TypeCheckErrorKind,
    ) -> ExprIdx {
        let expr_or_span = expr_or_span.into();
        let span = expr_or_span.span();

        self.push_error(span, label, help, kind);

        self.alloc_expr(
            Expr::new(Type::error(self.db), ExprData::Missing),
            expr_or_span,
        )
    }
    fn alloc_expr(&mut self, expr: Expr, ptr: impl Into<ExprOrSpan>) -> ExprIdx {
        let ptr = ptr.into();
        let idx = self.item.expr_arena.alloc(expr);
        self.source_map.expr_map_back.insert(idx, ptr.clone());
        self.source_map.expr_map.insert(ptr, idx);
        idx
    }
    pub fn check_boolean_exprs(
        &mut self,
        exprs: impl Iterator<Item = ast::CommaExpr>,
    ) -> Vec<ExprIdx> {
        let bool_ty = Type::bool(self.db).ghost(self.db);
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
    fn find_type(&self, ty: ast::Type) -> Type {
        crate::hir::find_type(self.db, self.program, ty)
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
                    let explicit_ty = it.ty().map(|ty| self.find_type(ty));
                    let initializer = self.check(it.span(), it.initializer());

                    let ty = if let Some(ty) = explicit_ty {
                        let span = it
                            .initializer()
                            .map(|i| i.span())
                            .unwrap_or_else(|| it.span());
                        self.expect_ty(span, ty, self.expr_ty(initializer));
                        ty
                    } else {
                        self.expr_ty(initializer)
                    }
                    .with_ghost(self.db, self.scope.is_ghost());

                    let var_span = name.span();
                    let variable = VariableRef::new(
                        self.declare_variable(VariableDeclaration::new_let(name), ty),
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
                _ => todo!(),
            })
            .collect();
        let (tail_expr, return_ty) = if let Some(tail_expr) = block.tail_expr() {
            let tail_expr = self.check(tail_expr.span(), Some(tail_expr));
            (
                Some(tail_expr),
                self.expr_ty(tail_expr)
                    .with_ghost(self.db, self.scope.is_ghost()),
            )
        } else {
            (
                None,
                Type::void(self.db).with_ghost(self.db, self.scope.is_ghost()),
            )
        };
        self.pop_scope();
        Block {
            stmts,
            tail_expr,
            return_ty,
        }
    }
    pub fn declare_variable(&mut self, decl: VariableDeclaration, ty: Type) -> VariableIdx {
        let name = decl.name.to_string();
        let var = self.item.declarations.alloc(
            decl,
            Variable::new(self.db, VariableId::new(self.db, name.clone())),
        );
        self.scope.insert(name.clone(), var);
        self.item.types.insert(var, ty);
        var
    }
    pub fn var_ty(&self, var: VariableIdx) -> Type {
        *self
            .item
            .types
            .get(var)
            .expect("VariableIdx was not in types map")
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
            self.declare_variable(VariableDeclaration::new_undefined(name.clone()), err_ty)
        }
    }

    fn find_named_type(&self, name: Ident) -> Type {
        crate::hir::find_named_type(self.db, self.program, name)
    }

    fn struct_fields(&self, s: crate::hir::Struct) -> Vec<Field> {
        crate::hir::struct_fields(self.db, self.program, s)
    }

    fn is_ghost(&self, e: ExprIdx) -> bool {
        self.expr_ty(e).is_ghost(self.db)
    }
}
pub fn check_param_list(
    db: &dyn crate::Db,
    program: Program,
    param_list: Option<ast::ParamList>,
) -> ParamList<Ident> {
    ParamList {
        params: param_list
            .map(|pl| {
                pl.params()
                    .map(|p| Param {
                        is_ghost: p.is_ghost(),
                        name: if let Some(name) = p.name() {
                            name.into()
                        } else {
                            todo!()
                        },
                        ty: if let Some(ty) = p.ty() {
                            crate::hir::find_type(db, program, ty.clone())
                        } else {
                            Type::new(db, TypeData::Error, None)
                        }
                        .with_ghost(db, p.is_ghost()),
                    })
                    .collect()
            })
            .unwrap_or_default(),
    }
}

impl hir::pretty::PrettyPrint for ItemContext {
    fn resolve_var(&self, idx: VariableIdx) -> Ident {
        self.declarations.map[idx].name.clone()
    }

    fn resolve_var_ty(&self, idx: VariableIdx) -> Type {
        self.var_ty(idx)
    }

    fn resolve_expr(&self, idx: ExprIdx) -> &Expr {
        &self.expr_arena[idx]
    }
}

impl hir::pretty::PrettyPrint for TypeCheckExpr<'_> {
    fn resolve_var(&self, idx: VariableIdx) -> Ident {
        self.item.declarations.map[idx].name.clone()
    }

    fn resolve_var_ty(&self, idx: VariableIdx) -> Type {
        self.var_ty(idx)
    }

    fn resolve_expr(&self, idx: ExprIdx) -> &Expr {
        &self.item.expr_arena[idx]
    }
}

impl ItemContext {
    pub fn pretty_expr(&self, db: &dyn crate::Db, expr: ExprIdx) -> String {
        hir::pretty::expr(self, db, expr)
    }
    pub fn pretty_ty(&self, db: &dyn crate::Db, ty: Type) -> String {
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
