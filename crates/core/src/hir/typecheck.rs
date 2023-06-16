mod expression;
mod typing;

use std::{collections::HashMap, sync::Arc};

use bitflags::bitflags;
use hir::item_context::Named;
use itertools::Itertools;
use miette::Diagnostic;
use mist_syntax::{
    ast::{self, HasAttrs, HasExpr, HasName, Spanned},
    ptr::AstPtr,
    SourceSpan,
};
use thiserror::Error;
use tracing::error;

use crate::{
    def::{Name, StructField},
    hir::{
        self, AssertionKind, Block, Condition, Decreases, Expr, ExprData, ExprIdx, Param,
        Statement, StatementData, Variable, VariableIdx,
    },
    types::{
        builtin::{error, ghost_bool, void},
        Field, TypeData, TypeId, TypeProvider, TypeTable, Typer,
    },
};

pub(crate) use typing::{TypingMut, TypingMutExt};

use super::{
    desugar,
    item_context::{FunctionContext, SpanOrAstPtr},
    ItemContext, ItemSourceMap, StatementId, TypeSrc,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VariableDeclarationKind {
    Let,
    Parameter,
    Function,
    Undefined,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariableDeclaration {
    name: Name,
    ast: AstPtr<ast::NameOrNameRef>,
    kind: VariableDeclarationKind,
}

impl VariableDeclaration {
    pub(crate) fn new_let(name: ast::Name) -> Self {
        let name = name.into();
        let ast = AstPtr::new(&name);
        VariableDeclaration { ast, name: name.into(), kind: VariableDeclarationKind::Let }
    }
    pub(crate) fn new_param(name: ast::Name) -> Self {
        let name = name.into();
        let ast = AstPtr::new(&name);
        VariableDeclaration { ast, name: name.into(), kind: VariableDeclarationKind::Parameter }
    }
    pub(crate) fn new_function(name: ast::Name) -> Self {
        let name = name.into();
        let ast = AstPtr::new(&name);
        VariableDeclaration { ast, name: name.into(), kind: VariableDeclarationKind::Function }
    }
    pub(crate) fn new_undefined(name: ast::NameRef) -> Self {
        let name = name.into();
        let ast = AstPtr::new(&name);
        VariableDeclaration { ast, name: name.into(), kind: VariableDeclarationKind::Undefined }
    }

    pub fn ast_name_or_name_ref(&self, root: &ast::SourceFile) -> ast::NameOrNameRef {
        self.ast.to_node(root.syntax())
    }
    pub fn name(&self) -> Name {
        self.name.clone()
    }

    pub fn kind(&self) -> VariableDeclarationKind {
        self.kind
    }
}

impl Spanned for &'_ VariableDeclaration {
    fn span(self) -> SourceSpan {
        (&self.ast).span()
    }
}

impl TypeId {
    pub(super) fn strip_ghost(self, typer: &mut impl TypingMut) -> TypeId {
        let data = typer.ty_data(self);
        if data.is_ghost {
            typer.alloc_ty_data(TypeData { is_ghost: false, kind: data.kind })
        } else {
            self
        }
    }
    pub(super) fn set_ghost(self, typer: &mut impl TypingMut, ghost: bool) -> TypeId {
        let data = typer.ty_data(self);
        if data.is_ghost != ghost {
            typer.alloc_ty_data(TypeData { is_ghost: ghost, kind: data.kind })
        } else {
            self
        }
    }
    /// If `ghost` is true, then the returned type id will definitely be ghost,
    /// otherwise, it will have the ghost label of `self`
    pub(super) fn with_ghost(self, typer: &mut impl TypingMut, ghost: bool) -> TypeId {
        if !ghost {
            return self;
        }
        self.set_ghost(typer, true)
    }
    pub(super) fn ghosted(self, typer: &mut impl TypingMut) -> TypeId {
        self.with_ghost(typer, true)
    }
    pub(super) fn is_ghost(self, typer: &impl TypeProvider) -> bool {
        typer.ty_data(self).is_ghost
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
    vars: HashMap<Name, VariableIdx>,
}

impl Scope {
    pub fn is_ghost(&self) -> bool {
        self.flags.is_ghost()
    }
    pub fn insert(&mut self, name: Name, var: VariableIdx) {
        self.vars.insert(name, var);
    }
    pub fn get(&mut self, name: &Name) -> Option<VariableIdx> {
        self.vars.get(name).copied()
    }
}

pub(crate) struct TypeChecker<'w> {
    db: &'w dyn crate::Db,
    scope: Scope,
    scope_stack: Vec<Scope>,
    source_map: ItemSourceMap,
    pub(super) cx: ItemContext,
    typer: Typer,
    field_tys: HashMap<Field, TypeSrc>,
}

impl hir::DefinitionHir {
    pub(crate) fn from_tc(db: &dyn crate::Db, mut tc: TypeChecker<'_>) -> Self {
        tc.cx.ty_table = Some(Arc::new(TypeTable::new(
            tc.typer.canonicalized().collect_vec(),
            tc.cx
                .file_context
                .struct_field_types
                .iter()
                .map(|(&f, &ty_src)| (f.into(), ty_src))
                .chain(tc.field_tys.iter().map(|(&f, &ty)| (f, ty)))
                .collect_vec()
                .into_iter()
                .map(|(f, ty)| (f, ty.ty(tc.db))),
        )));
        desugar::desugar(db, &mut tc.cx);

        hir::DefinitionHir::new(tc.db, tc.cx.def(), tc.cx, tc.source_map)
    }
}

impl<'a> TypeChecker<'a> {
    pub(crate) fn init(db: &'a dyn crate::Db, def: hir::Def) -> Self {
        let (fc, source_map) = super::file_context::initialize_file_context(db, def.file(db));

        let mut checker = Self {
            db,
            typer: fc.typer(),
            field_tys: Default::default(),
            scope: Default::default(),
            scope_stack: vec![],
            source_map,
            cx: ItemContext::new(def, fc),
        };

        let functions: HashMap<_, _> = checker
            .cx
            .file_context
            .function_types
            .values()
            .copied()
            .collect_vec()
            .into_iter()
            .map(|(f, f_ty)| {
                let f_ast = f.ast_node(db);
                let ty = checker.unsourced_ty(f_ty);

                (
                    f.name(db),
                    checker.declare_variable(
                        VariableDeclaration::new_function(f_ast.name().unwrap()),
                        ty,
                        f_ast.name().unwrap().span(),
                    ),
                )
            })
            .collect();

        let is_ghost = match def.kind(db) {
            hir::DefKind::Function(f) => f.ast_node(db).attr_flags().is_ghost(),
            hir::DefKind::TypeInvariant(_) => true,
            hir::DefKind::Struct(_) => false,
            hir::DefKind::StructField(_) => false,
        };

        if is_ghost {
            checker = checker.ghosted();
        }

        if let hir::DefKind::Function(f) = def.kind(db) {
            let f_ast = f.ast_node(db);
            let function_var = functions[&f.name(db)];

            checker.cx.params = f
                .param_list(db)
                .map(|p| {
                    let ty = checker
                        .expect_find_type_src(&p.ty)
                        .with_ghost(&mut checker, is_ghost || p.is_ghost);
                    let var = checker.declare_variable(
                        VariableDeclaration::new_param(p.name.clone()),
                        ty,
                        match p.ty {
                            Some(ty) => SpanOrAstPtr::from(&ty),
                            None => SpanOrAstPtr::Span(p.name.span()),
                        },
                    );
                    Param { is_ghost: p.is_ghost, name: var, ty }
                })
                .collect();

            checker.cx.return_ty = f_ast.ret().map(|ty| {
                let ty = checker.lower_type(&ty);
                checker.ghostify(ty, is_ghost)
            });

            let conditions = f_ast
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

            let decreases = checker.check_decreases(f_ast.decreases());

            checker.cx.function_context = Some(FunctionContext {
                function_var,
                conditions,
                decreases,
                return_ty_src: checker.cx.return_ty,
            });

            if !f_ast.is_ghost() && f_ast.body().is_none() {
                checker.ty_error(
                    f_ast
                        .semicolon_token()
                        .map(|t| t.span())
                        .unwrap_or_else(|| f_ast.name().unwrap().span()),
                    None,
                    None,
                    TypeCheckErrorKind::NonGhostFunctionWithoutBody,
                );
            }
        }

        checker.cx.self_ty = match def.kind(db) {
            hir::DefKind::TypeInvariant(ty_inv) => ty_inv.ast_node(db).name_ref().map(|name| {
                checker.unsourced_ty(checker.find_named_type(name.span(), name.into()))
            }),
            hir::DefKind::Struct(s) => s.ast_node(db).name().map(|name| {
                checker.unsourced_ty(checker.find_named_type(name.span(), name.into()))
            }),
            hir::DefKind::StructField(_) => None,
            hir::DefKind::Function(_) => None,
        };

        checker
    }

    pub fn set_body_expr_from_block(&mut self, block: Block, node: ast::BlockExpr) {
        let idx = self.alloc_expr(Expr::new_block(block), &ast::Expr::from(node));
        self.cx.body_expr = Some(idx);
    }
    pub fn set_return_ty(&mut self, ty: TypeSrc) {
        self.cx.return_ty = Some(ty);
    }

    pub fn ghosted(mut self) -> Self {
        debug_assert!(
            self.scope_stack.is_empty(),
            "Tried to make a checker ghost, while it was in operation"
        );
        if let Some(ty) = self.cx.return_ty {
            self.cx.return_ty = Some(self.ghostify(ty, true));
        }
        self.scope.flags |= ScopeFlags::GHOST;
        self
    }
    fn push_scope(&mut self, f: impl FnOnce(ScopeFlags) -> ScopeFlags) {
        self.scope_stack.push(self.scope.clone());
        self.scope.flags = f(self.scope.flags);
    }
    fn pop_scope(&mut self) {
        self.scope = self.scope_stack.pop().expect("tried to pop scope while none was pushed");
    }
    pub fn expr_ty(&self, expr: ExprIdx) -> TypeId {
        self.cx.expr_ty(expr).id()
    }
    pub fn expr_span(&self, expr: ExprIdx) -> SourceSpan {
        self.source_map.expr_span(&self.cx, expr)
    }
    pub fn check(&mut self, fallback_span: impl Spanned, expr: Option<ast::Expr>) -> ExprIdx {
        expression::check_opt(self, fallback_span, expr)
    }
    pub(crate) fn pretty_ty(&self, ty: TypeId) -> String {
        hir::pretty::ty(self, self.db, false, ty)
    }
    pub fn expect_ty(&mut self, span: impl Spanned, expected: TypeId, actual: TypeId) -> TypeId {
        match self.unify_inner(expected, actual) {
            Some(x) => x,
            None => self.ty_error(
                span.span(),
                None,
                None,
                TypeCheckErrorKind::Mismatch {
                    expected: self.pretty_ty(expected),
                    actual: self.pretty_ty(actual),
                },
            ),
        }
    }
    fn unify(&mut self, span: impl Spanned, t1: TypeId, t2: TypeId) -> TypeId {
        match self.unify_inner(t1, t2) {
            Some(x) => x,
            None => self.ty_error(
                span,
                None,
                None,
                TypeCheckErrorKind::CantUnify(self.pretty_ty(t1), self.pretty_ty(t2)),
            ),
        }
    }
    fn unify_inner(&mut self, expected: TypeId, actual: TypeId) -> Option<TypeId> {
        self.typer.unify(expected, actual)
    }
    fn expr_error(
        &mut self,
        expr_or_span: impl Into<SpanOrAstPtr<ast::Expr>>,
        label: Option<String>,
        help: Option<String>,
        kind: TypeCheckErrorKind,
    ) -> ExprIdx {
        let expr_or_span = expr_or_span.into();

        self.ty_error(&expr_or_span, label, help, kind);

        self.alloc_expr(ExprData::Missing.typed(error()), expr_or_span)
    }
    pub(super) fn alloc_expr(
        &mut self,
        expr: Expr,
        ptr: impl Into<SpanOrAstPtr<ast::Expr>>,
    ) -> ExprIdx {
        let ptr = ptr.into();
        let idx = self.cx.expr_arena.alloc(expr);
        self.source_map.register_expr(ptr, idx).unwrap();
        idx
    }
    pub fn check_boolean_exprs(
        &mut self,
        exprs: impl Iterator<Item = ast::CommaExpr>,
    ) -> Vec<ExprIdx> {
        exprs
            .map(|comma_expr| {
                let expr = self.check(&comma_expr, comma_expr.expr());
                self.expect_ty(&comma_expr, ghost_bool(), self.expr_ty(expr));
                expr
            })
            .collect()
    }
    fn alloc_stmt(&mut self, src: AstPtr<ast::Stmt>, data: StatementData) -> StatementId {
        let id = self.cx.stmt_arena.alloc(Statement::new(data));
        self.source_map.register_stmt(src, id).unwrap();
        id
    }
    fn check_assertion(
        &mut self,
        src: AstPtr<ast::Stmt>,
        kind: AssertionKind,
        exprs: impl Iterator<Item = ast::CommaExpr>,
    ) -> StatementId {
        let exprs = self.check_boolean_exprs(exprs);
        self.alloc_stmt(src, StatementData::Assertion { kind, exprs })
    }
    fn check_decreases(&mut self, decreases: Option<ast::Decreases>) -> Decreases {
        if let Some(d) = decreases {
            if d.underscore_token().is_some() {
                Decreases::Inferred
            } else {
                Decreases::Expr(self.check(&d, d.expr()))
            }
        } else {
            Decreases::Unspecified
        }
    }
    fn check_stmt(&mut self, stmt: ast::Stmt) -> StatementId {
        let ptr = AstPtr::new(&stmt);
        let data = match stmt {
            ast::Stmt::LetStmt(it) => {
                let name = it.name().unwrap();
                let explicit_ty = it.ty().map(|ty| self.lower_type(&ty));
                let initializer = self.check(&it, it.initializer());

                let ty = if let Some(ty) = explicit_ty {
                    let ty = ty.ty(self.db);
                    let span = it.initializer().map(|i| i.span()).unwrap_or_else(|| it.span());
                    self.expect_ty(span, ty, self.expr_ty(initializer));
                    ty
                } else {
                    self.expr_ty(initializer)
                }
                .with_ghost(self, self.scope.is_ghost());

                let var_span = name.span();
                let var_ty = explicit_ty.unwrap_or_else(|| self.unsourced_ty(ty));
                let variable = self.declare_variable(
                    VariableDeclaration::new_let(name),
                    var_ty,
                    match it.ty() {
                        Some(ty) => SpanOrAstPtr::from(&ty),
                        None => SpanOrAstPtr::from(var_span),
                    },
                );

                StatementData::Let { variable, explicit_ty, initializer }
            }
            ast::Stmt::Item(it) => StatementData::Expr(self.expr_error(
                it.span(),
                None,
                None,
                TypeCheckErrorKind::NotYetImplemented("items in statement position".to_string()),
            )),
            ast::Stmt::ExprStmt(it) => StatementData::Expr(self.check(&it, it.expr())),
            ast::Stmt::AssertStmt(it) => {
                return self.check_assertion(ptr, AssertionKind::Assert, it.comma_exprs())
            }
            ast::Stmt::AssumeStmt(it) => {
                return self.check_assertion(ptr, AssertionKind::Assume, it.comma_exprs())
            }
        };
        self.alloc_stmt(ptr, data)
    }
    pub fn check_block(
        &mut self,
        block: &ast::BlockExpr,
        f: impl FnOnce(ScopeFlags) -> ScopeFlags,
    ) -> Block {
        self.push_scope(f);
        let stmts = block.statements().map(|stmt| self.check_stmt(stmt)).collect();
        let (tail_expr, return_ty) = if let Some(tail_expr) = block.tail_expr() {
            let tail_expr = self.check(tail_expr.span(), Some(tail_expr));
            (Some(tail_expr), self.expr_ty(tail_expr).with_ghost(self, self.scope.is_ghost()))
        } else {
            (None, void().with_ghost(self, self.scope.is_ghost()))
        };
        self.pop_scope();
        Block { stmts, tail_expr, return_ty: return_ty.ty(self) }
    }
    pub fn declare_variable(
        &mut self,
        decl: VariableDeclaration,
        ty: TypeSrc,
        ty_span: impl Into<SpanOrAstPtr<ast::Type>>,
    ) -> VariableIdx {
        let name = decl.name();
        let ast = decl.ast.clone();
        let var = self.cx.declarations.alloc(decl, Variable::new(self.db, name.clone(), ty));
        self.source_map.register_name(ast, Named::Variable(var)).unwrap();
        self.scope.insert(name, var);
        let ty_src = ty_span.into();
        self.source_map.register_ty_src(ty, ty_src).unwrap();
        var
    }
    pub fn var_ty(&self, var: VariableIdx) -> TypeId {
        self.cx.var_ty(self.db, var).id()
    }
    pub fn lookup_name(&mut self, name: &ast::NameRef) -> VariableIdx {
        if let Some(var) = self.scope.get(&name.clone().into()) {
            let ast = AstPtr::new(&name.clone().into());
            self.source_map.register_name(ast, Named::Variable(var)).unwrap();
            var
        } else {
            let err_ty = self.ty_error(
                name,
                None,
                None,
                TypeCheckErrorKind::UndefinedVariable(name.to_string()),
            );
            let ty = self.unsourced_ty(err_ty);
            self.declare_variable(VariableDeclaration::new_undefined(name.clone()), ty, name.span())
        }
    }

    fn struct_fields(&self, s: crate::hir::Struct) -> impl Iterator<Item = StructField> + 'a {
        s.fields(self.db)
    }

    fn is_ghost(&self, e: ExprIdx) -> bool {
        self.expr_ty(e).is_ghost(self)
    }

    pub(super) fn ghostify(&mut self, ts: TypeSrc, is_ghost: bool) -> TypeSrc {
        ts.with_ghost(self, is_ghost)
    }

    fn return_ty(&self) -> TypeId {
        self.cx.return_ty.map(|ty| ty.ty(self.db)).unwrap_or_else(void)
    }

    fn self_ty(&self) -> Option<TypeId> {
        self.cx.self_ty.map(|ty| ty.ty(self.db))
    }
}

impl<'a> TypeProvider for TypeChecker<'a> {
    fn ty_data(&self, ty: TypeId) -> TypeData {
        self.typer.probe_type(ty)
    }

    fn struct_field_ty(&self, f: StructField) -> TypeId {
        self.field_tys[&f.into()].ty(self.db)
    }
}

impl<'a> TypingMut for TypeChecker<'a> {
    fn db(&self) -> &dyn crate::Db {
        self.db
    }

    fn push_error(&self, err: TypeCheckError) {
        TypeCheckErrors::push(self.db, err);
    }

    fn lookup_named_ty(&self, name: Name) -> Option<TypeId> {
        self.cx.file_context.named_types.get(&name).copied()
    }

    fn new_free(&mut self) -> TypeId {
        self.typer.new_free()
    }

    fn alloc_ty_data(&mut self, data: TypeData) -> TypeId {
        self.typer.ty_id(data)
    }

    fn alloc_ty_src(&mut self, ts: TypeSrc, ty_src: Option<SpanOrAstPtr<ast::Type>>) -> TypeSrc {
        if let Some(src) = ty_src {
            self.source_map.register_ty_src(ts, src).unwrap();
        }
        ts
    }
}

pub(crate) trait Typed {
    fn with_ghost(self, typing: &mut impl TypingMut, ghost: bool) -> Self
    where
        Self: Sized;
    fn ty(&self, tc: &impl TypingMut) -> TypeId;
}

impl Typed for TypeId {
    fn with_ghost(self, typing: &mut impl TypingMut, ghost: bool) -> Self
    where
        Self: Sized,
    {
        if ghost {
            let data = typing.ty_data(self);
            if data.is_ghost {
                self
            } else {
                typing.alloc_ty_data(TypeData { is_ghost: true, kind: data.kind })
            }
        } else {
            self
        }
    }
    fn ty(&self, _tc: &impl TypeProvider) -> TypeId {
        *self
    }
}
impl Typed for TypeSrc {
    fn with_ghost(self, typing: &mut impl TypingMut, ghost: bool) -> Self
    where
        Self: Sized,
    {
        if ghost {
            if typing.ty_data(self.ty(typing.db())).is_ghost {
                self
            } else {
                let ty = self.ty(typing.db()).with_ghost(typing, ghost);
                typing.unsourced_ty(ty)
            }
        } else {
            self
        }
    }
    fn ty(&self, tc: &impl TypingMut) -> TypeId {
        TypeSrc::ty(*self, tc.db())
    }
}

impl hir::pretty::PrettyPrint for ItemContext {
    fn resolve_var(&self, idx: VariableIdx) -> Name {
        self.declarations.map[idx].name.clone()
    }

    fn resolve_var_ty(&self, db: &dyn crate::Db, idx: VariableIdx) -> TypeId {
        self.var_ty(db, idx).id()
    }

    fn resolve_expr(&self, idx: ExprIdx) -> &Expr {
        &self.expr_arena[idx]
    }

    fn resolve_ty(&self, ty: TypeId) -> TypeData {
        self.ty_data(ty)
    }

    fn resolve_src_ty(&self, db: &dyn crate::Db, ts: TypeSrc) -> TypeId {
        ts.ty(db)
    }
}

impl hir::pretty::PrettyPrint for TypeChecker<'_> {
    fn resolve_var(&self, idx: VariableIdx) -> Name {
        self.cx.declarations.map[idx].name.clone()
    }

    fn resolve_var_ty(&self, _db: &dyn crate::Db, idx: VariableIdx) -> TypeId {
        self.var_ty(idx)
    }

    fn resolve_expr(&self, idx: ExprIdx) -> &Expr {
        &self.cx.expr_arena[idx]
    }

    fn resolve_ty(&self, ty: TypeId) -> TypeData {
        self.typer.probe_type(ty)
    }

    fn resolve_src_ty(&self, db: &dyn crate::Db, ts: TypeSrc) -> TypeId {
        ts.ty(db)
    }
}

impl ItemContext {
    pub fn pretty_expr(&self, db: &dyn crate::Db, expr: ExprIdx) -> String {
        hir::pretty::expr(self, db, expr)
    }
    pub fn pretty_ty(&self, db: &dyn crate::Db, ty: TypeId) -> String {
        hir::pretty::ty(self, db, false, ty)
    }
}

#[salsa::accumulator]
pub struct TypeCheckErrors(TypeCheckError);

#[derive(Debug, Diagnostic, Clone, Eq, PartialEq, Error)]
#[error("{kind}")]
pub struct TypeCheckError {
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
    UnknownStructField { field: Name, strukt: Name },
    #[error("not yet implemented: {0}")]
    NotYetImplemented(String),
    #[error("no struct with name `{name}` was found")]
    UnknownStruct { name: Name },
    #[error("`ghost` was used where only non-ghost can be used")]
    GhostUsedInNonGhost,
    #[error("only `ghost` functions can be declared without a body")]
    NonGhostFunctionWithoutBody,
    #[error("functions called in `ghost` functions must be either `ghost`, `pure`, or both")]
    NonGhostNorPureCalledInGhost,
    #[error("tried to assign a `ghost` value to a variable that is not marked `ghost`")]
    GhostAssignedToNonGhost,
    #[error("invalid left-hand-side of assignment")]
    InvalidLhsOfAssignment,
}
