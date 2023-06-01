mod expression;
mod typer;

use std::{collections::HashMap, sync::Arc};

use bitflags::bitflags;
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
    def::StructField,
    hir::{
        self, AssertionKind, Block, Condition, Decreases, Expr, ExprData, ExprIdx, Field, Name,
        Param, Primitive, Statement, StatementData, TypeData, Variable, VariableId, VariableIdx,
        VariableRef,
    },
};

pub use typer::{builtin, TypeId};
use typer::{builtin::*, Typer};

use super::{
    item_context::{FunctionContext, SpanOrAstPtr},
    types::TypeProvider,
    ItemContext, ItemSourceMap, TypeSrc, TypeSrcId, TypeTable,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariableDeclaration {
    name: Name,
    ast: AstPtr<ast::NameOrNameRef>,
    kind: VariableDeclarationKind,
}

impl VariableDeclaration {
    pub(crate) fn new_let(name: ast::Name) -> Self {
        let name = ast::NameOrNameRef::Name(name);
        let ast = AstPtr::new(&name);
        VariableDeclaration {
            ast,
            name: name.into(),
            kind: VariableDeclarationKind::Let,
        }
    }
    pub(crate) fn new_param(name: ast::Name) -> Self {
        let name = ast::NameOrNameRef::Name(name);
        let ast = AstPtr::new(&name);
        VariableDeclaration {
            ast,
            name: name.into(),
            kind: VariableDeclarationKind::Parameter,
        }
    }
    pub(crate) fn new_function(name: ast::Name) -> Self {
        let name = ast::NameOrNameRef::Name(name);
        let ast = AstPtr::new(&name);
        VariableDeclaration {
            ast,
            name: name.into(),
            kind: VariableDeclarationKind::Function,
        }
    }
    pub(crate) fn new_undefined(name: ast::NameRef) -> Self {
        let name = ast::NameOrNameRef::NameRef(name);
        let ast = AstPtr::new(&name);
        VariableDeclaration {
            ast,
            name: name.into(),
            kind: VariableDeclarationKind::Undefined,
        }
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
    pub(super) fn tc_strip_ghost(self, typer: &mut Typer) -> TypeId {
        match typer.probe_type(self) {
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
    pub(super) fn tc_is_ghost(self, typer: &mut Typer) -> bool {
        matches!(typer.probe_type(self), TypeData::Ghost(_))
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

pub struct TypeChecker<'w> {
    db: &'w dyn crate::Db,
    scope: Scope,
    scope_stack: Vec<Scope>,
    source_map: ItemSourceMap,
    pub(super) cx: ItemContext,
    typer: Typer,
    field_tys: HashMap<Field, TypeSrcId>,
}

impl From<TypeChecker<'_>> for hir::DefinitionHir {
    fn from(mut tc: TypeChecker<'_>) -> Self {
        tc.cx.ty_table = Arc::new(TypeTable::new(
            tc.typer.canonicalized().collect_vec(),
            tc.cx
                .structs
                .values()
                .flat_map(|fields| fields.iter().map(|&(f, ty_src)| (f.into(), ty_src)))
                .chain(tc.field_tys.iter().map(|(&f, &ty)| (f, ty)))
                .collect_vec()
                .into_iter()
                .map(|(f, ty)| (f, ty.ty(&mut tc))),
        ));

        hir::DefinitionHir::new(tc.db, tc.cx.def(), tc.cx, tc.source_map)
    }
}

impl<'a> TypeChecker<'a> {
    pub(crate) fn init(db: &'a dyn crate::Db, def: hir::Def) -> Self {
        let typer = Typer::new();
        let mut checker = Self {
            db,
            typer,
            field_tys: Default::default(),
            scope: Default::default(),
            scope_stack: vec![],
            source_map: Default::default(),
            cx: ItemContext::new(def),
        };

        let is_ghost = match def.kind(db) {
            hir::DefKind::Function(f) => f.ast_node(db).attr_flags().is_ghost(),
            hir::DefKind::TypeInvariant(_) => true,
            hir::DefKind::Struct(_) => false,
            hir::DefKind::StructField(_) => false,
        };

        if is_ghost {
            checker = checker.ghosted();
        }

        for def in hir::file_definitions(db, def.file(db)) {
            let f = match def.kind(db) {
                hir::DefKind::Function(f) => f,
                hir::DefKind::Struct(s) => {
                    let s_ast = s.ast_node(db);

                    let s_ty = *checker
                        .cx
                        .named_types
                        .entry(s.name(db))
                        .or_insert_with(|| checker.typer.ty_id(TypeData::Struct(s)));
                    if let Some(name) = s_ast.name() {
                        let ts = checker.alloc_type_src(
                            TypeSrc {
                                data: Some(TypeData::Struct(s)),
                                ty: s_ty,
                            },
                            name.span(),
                        );
                        checker.cx.struct_types.insert(s, ts);
                    }

                    let fields = s
                        .fields(db)
                        .map(|f| {
                            let data = f.ast_node(db).ty();
                            let ty = checker.expect_find_type_src(&data);
                            let ty_id = *checker.field_tys.entry(f.into()).or_insert_with(|| ty);
                            (f, ty_id)
                        })
                        .collect();
                    checker.cx.structs.insert(s, fields);

                    continue;
                }
                _ => continue,
            };
            let is_ghost = f.attrs(db).is_ghost();
            let f_ast = f.ast_node(db);

            let params = f
                .param_list(db)
                .map(|param| {
                    let ty = checker.expect_find_type_src(&param.ty);
                    Param {
                        is_ghost: param.is_ghost,
                        name: param.name.into(),
                        ty: checker.ghostify(ty, is_ghost),
                    }
                })
                .collect();
            let return_ty_src = f_ast.ret().map(|ty| {
                checker
                    .find_type_src(&ty)
                    .with_ghost(is_ghost)
                    .ts(&mut checker)
            });
            let return_ty = return_ty_src
                .map(|ts| checker.cx[ts].ty)
                .unwrap_or_else(void)
                .with_ghost(is_ghost)
                .ty(&mut checker);

            if let Some(name) = f_ast.name() {
                let ty = checker.ty_id(TypeData::Function {
                    attrs: f.attrs(db),
                    name: Some(f.name(db).clone()),
                    params,
                    return_ty,
                });
                let ts = checker.unsourced_ty(ty);
                let name_span = name.span();
                let var = checker.declare_variable(
                    VariableDeclaration::new_function(name),
                    ts,
                    name_span,
                );

                if let hir::DefKind::Function(_) = def.kind(db) {
                    checker.cx.function_context = Some(FunctionContext {
                        function_var: VariableRef::new(var, name_span),
                        decreases: Default::default(),
                        conditions: vec![],
                        return_ty_src,
                    });
                }
            }
        }

        if let hir::DefKind::Function(f) = def.kind(db) {
            let f_ast = f.ast_node(db);

            checker.cx.params = f
                .param_list(db)
                .map(|p| {
                    let ty = checker
                        .expect_find_type_src(&p.ty)
                        .with_ghost(is_ghost || p.is_ghost)
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

            checker.cx.return_ty = f_ast.ret().map(|ty| {
                let ty = checker.find_type_src(&ty);
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

            if let Some(cx) = &mut checker.cx.function_context {
                cx.conditions = conditions;
                cx.decreases = decreases;
            }

            if !f_ast.is_ghost() && f_ast.body().is_none() {
                checker.push_error(
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

    pub fn ty_id(&mut self, td: TypeData) -> TypeId {
        self.typer.ty_id(td)
    }

    pub fn set_body_expr_from_block(&mut self, block: Block, node: ast::BlockExpr) {
        let idx = self.alloc_expr(Expr::new_block(block), &ast::Expr::from(node));
        self.cx.body_expr = Some(idx);
    }
    pub fn set_return_ty(&mut self, ty: TypeSrcId) {
        self.cx.return_ty = Some(ty);
    }
    pub fn set_self_ty(&mut self, ty: TypeSrcId) {
        self.cx.self_ty = Some(ty);
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
        self.scope = self
            .scope_stack
            .pop()
            .expect("tried to pop scope while none was pushed");
    }
    pub fn expr_ty(&self, expr: ExprIdx) -> TypeId {
        self.cx.expr_arena[expr].ty
    }
    pub fn expr_span(&self, expr: ExprIdx) -> SourceSpan {
        self.source_map.expr_map_back[expr].span()
    }
    pub fn check(&mut self, fallback_span: impl Spanned, expr: Option<ast::Expr>) -> ExprIdx {
        expression::check_opt(self, fallback_span, expr)
    }

    fn ty_data(&self, ty: TypeId) -> TypeData {
        self.typer.probe_type(ty)
    }
    pub(crate) fn pretty_ty(&self, ty: TypeId) -> String {
        hir::pretty::ty(self, self.db, ty)
    }
    pub fn expect_ty(
        &mut self,
        span: impl Spanned,
        expected: impl Typed,
        actual: impl Typed,
    ) -> TypeId {
        let expected = expected.ty(self);
        let actual = actual.ty(self);
        match self.unify_inner(expected, actual) {
            Some(x) => x,
            None => self.push_error(
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
    fn unify(&mut self, span: impl Spanned, t1: impl Typed, t2: impl Typed) -> TypeId {
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

        self.typer.unify(expected, actual)
    }
    fn push_error(
        &self,
        span: impl Spanned,
        label: Option<String>,
        help: Option<String>,
        kind: TypeCheckErrorKind,
    ) -> TypeId {
        let span = span.span();
        let err = TypeCheckError {
            input: self.cx.def.file(self.db).text(self.db).clone(),
            span,
            label,
            help,
            kind,
        };
        TypeCheckErrors::push(self.db, err);
        // eprintln!("{:?}", miette::Error::new(err));
        error()
    }
    fn expr_error(
        &mut self,
        expr_or_span: impl Into<SpanOrAstPtr<ast::Expr>>,
        label: Option<String>,
        help: Option<String>,
        kind: TypeCheckErrorKind,
    ) -> ExprIdx {
        let expr_or_span = expr_or_span.into();

        self.push_error(&expr_or_span, label, help, kind);

        self.alloc_expr(ExprData::Missing.typed(error()), expr_or_span)
    }
    pub(super) fn alloc_expr(
        &mut self,
        expr: Expr,
        ptr: impl Into<SpanOrAstPtr<ast::Expr>>,
    ) -> ExprIdx {
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
        exprs
            .map(|comma_expr| {
                let expr = self.check(&comma_expr, comma_expr.expr());
                self.expect_ty(&comma_expr, ghost_bool(), self.expr_ty(expr));
                expr
            })
            .collect()
    }
    fn check_assertion(
        &mut self,
        span: impl Spanned,
        kind: AssertionKind,
        exprs: impl Iterator<Item = ast::CommaExpr>,
    ) -> Statement {
        Statement::new(
            span.span(),
            StatementData::Assertion {
                kind,
                exprs: self.check_boolean_exprs(exprs),
            },
        )
    }
    pub(super) fn find_type_src(&mut self, ast_ty: &ast::Type) -> TypeSrcId {
        let (td, ty) = match ast_ty {
            mist_syntax::ast::Type::NamedType(ast_name) => {
                let name = ast_name.name().unwrap();
                let ty = self.find_named_type(ast_name, name.into());
                let td = match self.ty_data(ty) {
                    TypeData::Struct(s) => TypeData::Struct(s),
                    TypeData::Error => TypeData::Error,
                    _ => todo!(),
                };
                (td, ty)
            }
            mist_syntax::ast::Type::Primitive(it) => match () {
                _ if it.int_token().is_some() => (TypeData::Primitive(Primitive::Int), int()),
                _ if it.bool_token().is_some() => (TypeData::Primitive(Primitive::Bool), bool()),
                _ => {
                    todo!();
                    // TypeData::Error
                }
            },
            mist_syntax::ast::Type::Optional(it) => {
                let inner = if let Some(ty) = it.ty() {
                    self.find_type_src(&ty)
                } else {
                    let ty = self.new_free();
                    self.unsourced_ty(ty)
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
                    let ty = self.new_free();
                    self.unsourced_ty(ty)
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
                Decreases::Expr(self.check(&d, d.expr()))
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
                    let initializer = self.check(&it, it.initializer());

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
                    let var_ty = explicit_ty.unwrap_or_else(|| self.unsourced_ty(ty));
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
                ast::Stmt::ExprStmt(it) => {
                    Statement::new(it.span(), StatementData::Expr(self.check(&it, it.expr())))
                }
                ast::Stmt::AssertStmt(it) => {
                    self.check_assertion(&it, AssertionKind::Assert, it.comma_exprs())
                }
                ast::Stmt::AssumeStmt(it) => {
                    self.check_assertion(&it, AssertionKind::Assume, it.comma_exprs())
                }
                ast::Stmt::WhileStmt(it) => Statement::new(
                    it.span(),
                    StatementData::While {
                        expr: self.check(&it, it.expr()),
                        invariants: it
                            .invariants()
                            .map(|inv| self.check_boolean_exprs(inv.comma_exprs()))
                            .collect(),
                        decreases: self.check_decreases(it.decreases()),
                        body: if let Some(block) = it.block_expr() {
                            self.check_block(&block, id)
                        } else {
                            Block {
                                stmts: Vec::new(),
                                tail_expr: None,
                                return_ty: void(),
                            }
                        },
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
            (None, void().with_ghost(self.scope.is_ghost()))
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
        let name = decl.name();
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
    pub fn lookup_name(&mut self, name: &ast::NameRef) -> VariableIdx {
        if let Some(var) = self.scope.get(&name.clone().into()) {
            var
        } else {
            let err_ty = self.push_error(
                name,
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

    pub(super) fn find_named_type(&self, span: impl Spanned, name: Name) -> TypeId {
        self.cx.named_types.get(&name).copied().unwrap_or_else(|| {
            self.push_error(
                span,
                None,
                None,
                TypeCheckErrorKind::UndefinedType(name.to_string()),
            )
        })
    }

    fn struct_fields(&self, s: crate::hir::Struct) -> impl Iterator<Item = StructField> + 'a {
        s.fields(self.db)
    }

    fn is_ghost(&mut self, e: ExprIdx) -> bool {
        self.expr_ty(e).tc_is_ghost(&mut self.typer)
    }

    pub(super) fn unsourced_ty(&mut self, ty: impl Typed) -> TypeSrcId {
        let ty = ty.ty(self);
        self.cx.ty_src_arena.alloc(TypeSrc { data: None, ty })
    }

    pub(super) fn ghostify(&mut self, ts: TypeSrcId, is_ghost: bool) -> TypeSrcId {
        let ty = self.cx[ts].ty;
        if is_ghost && !ty.tc_is_ghost(&mut self.typer) {
            self.unsourced_ty(ty.ghost())
        } else {
            ts
        }
    }

    fn return_ty(&self) -> TypeId {
        self.cx
            .return_ty
            .map(|ty| self.cx[ty].ty)
            .unwrap_or_else(void)
    }

    fn self_ty(&self) -> Option<TypeId> {
        self.cx.self_ty.map(|ty| self.cx[ty].ty)
    }

    pub(super) fn expect_find_type(&mut self, ty: &Option<ast::Type>) -> TypeId {
        match ty {
            Some(ty) => {
                let ts = self.find_type_src(ty);
                self.cx[ts].ty
            }
            None => error(),
        }
    }
    pub(super) fn expect_find_type_src(&mut self, ty: &Option<ast::Type>) -> TypeSrcId {
        match ty {
            Some(ty) => self.find_type_src(ty),
            None => self.unsourced_ty(error()),
        }
    }

    fn new_free(&mut self) -> TypeId {
        self.typer.new_free()
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
            if ty.tc_is_ghost(&mut tc.typer) {
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
    fn resolve_var(&self, idx: VariableIdx) -> Name {
        self.declarations.map[idx].name.clone()
    }

    fn resolve_var_ty(&self, idx: VariableIdx) -> TypeId {
        self.var_ty(idx).id()
    }

    fn resolve_expr(&self, idx: ExprIdx) -> &Expr {
        &self.expr_arena[idx]
    }

    fn resolve_ty(&self, ty: TypeId) -> TypeData {
        if self.ty_table.contains_ty(ty) {
            self.ty_table.ty_data(ty).map(|t| t.id())
        } else {
            error!(?ty, "tried to get type id which was not in ItemContext");
            TypeData::Error
        }
    }

    fn resolve_src_ty(&self, ts: TypeSrcId) -> TypeId {
        self.ty_src_arena[ts].ty
    }
}

impl hir::pretty::PrettyPrint for TypeChecker<'_> {
    fn resolve_var(&self, idx: VariableIdx) -> Name {
        self.cx.declarations.map[idx].name.clone()
    }

    fn resolve_var_ty(&self, idx: VariableIdx) -> TypeId {
        self.var_ty(idx)
    }

    fn resolve_expr(&self, idx: ExprIdx) -> &Expr {
        &self.cx.expr_arena[idx]
    }

    fn resolve_ty(&self, ty: TypeId) -> TypeData {
        self.typer.probe_type(ty)
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
