pub mod source_map;

use std::sync::Arc;

use derive_new::new;
use mist_syntax::{ast::Spanned, ptr::AstPtr, SourceSpan};

use crate::{
    def::{Name, StructField},
    types::{Adt, AdtField, TypeData, TypeId, TypeProvider, TypeTable},
    util::{IdxArena, IdxMap, IdxWrap},
    VariableDeclaration,
};

use super::{
    file_context::FileContext, Condition, Decreases, Def, Expr, ExprIdx, Param, Statement,
    StatementId, TypeSrc, Variable, VariableIdx,
};

#[derive(new, Debug, Clone, PartialEq, Eq)]
pub struct ItemContext {
    def: Def,
    pub(super) file_context: FileContext,

    #[new(default)]
    pub(super) function_context: Option<FunctionContext>,
    #[new(default)]
    pub(super) declarations: Trace<VariableIdx, VariableDeclaration>,
    #[new(default)]
    pub(super) stmt_arena: IdxArena<StatementId>,
    #[new(default)]
    pub(super) expr_arena: IdxArena<ExprIdx>,

    #[new(default)]
    pub(super) ty_table: Option<Arc<TypeTable>>,

    #[new(default)]
    pub(super) params: Vec<Param<VariableIdx, TypeSrc>>,
    #[new(default)]
    pub(super) body_expr: Option<ExprIdx>,
    #[new(default)]
    pub(super) return_ty: Option<TypeSrc>,
    #[new(default)]
    pub(super) invariant_ty: Option<TypeSrc>,

    #[new(default)]
    pub(super) desugared: IdxMap<ExprIdx, ExprIdx>,
    #[new(default)]
    pub(super) desugared_back: IdxMap<ExprIdx, ExprIdx>,
}

impl std::ops::Index<ExprIdx> for ItemContext {
    type Output = Expr;

    fn index(&self, index: ExprIdx) -> &Self::Output {
        &self.expr_arena[index]
    }
}
impl std::ops::Index<StatementId> for ItemContext {
    type Output = Statement;

    fn index(&self, index: StatementId) -> &Self::Output {
        &self.stmt_arena[index]
    }
}
impl std::ops::Index<VariableIdx> for ItemContext {
    type Output = Variable;

    fn index(&self, index: VariableIdx) -> &Self::Output {
        &self.declarations.arena[index]
    }
}

impl ItemContext {
    pub fn def(&self) -> Def {
        self.def
    }
    pub fn function_context(&self) -> Option<&FunctionContext> {
        self.function_context.as_ref()
    }
    pub fn function_var(&self) -> Option<VariableIdx> {
        self.function_context.as_ref().map(|cx| cx.function_var)
    }
    pub fn conditions(&self) -> impl Iterator<Item = &Condition> {
        self.function_context.iter().flat_map(|cx| &cx.conditions)
    }
    pub fn params(&self) -> &[Param<VariableIdx, TypeSrc>] {
        &self.params
    }
    pub fn return_ty(&self, db: &dyn crate::Db) -> Option<TypeId> {
        self.return_ty.map(|ts| ts.ty(db))
    }
    pub fn invariant_ty(&self, db: &dyn crate::Db) -> Option<TypeId> {
        self.invariant_ty.map(|ts| ts.ty(db))
    }
    pub fn body_expr(&self) -> Option<ExprIdx> {
        self.body_expr
    }
    pub fn var(&self, var: VariableIdx) -> Variable {
        self.declarations.arena[var]
    }
    pub fn var_ty(&self, db: &dyn crate::Db, var: VariableIdx) -> TypeId {
        self.var(var).ty(db)
    }
    /// Returns the original expr, without going through the desugared table
    pub fn original_expr(&self, expr: ExprIdx) -> &Expr {
        &self.expr_arena[expr]
    }
    pub fn expr(&self, expr: ExprIdx) -> &Expr {
        if let Some(desugared) = self.desugared.get(expr) {
            &self.expr_arena[*desugared]
        } else {
            &self.expr_arena[expr]
        }
    }
    pub fn expr_ty(&self, expr: ExprIdx) -> TypeId {
        self.expr_arena[expr].ty
    }
    pub fn decl(&self, var: VariableIdx) -> &VariableDeclaration {
        &self.declarations.map[var]
    }
    pub fn var_decl_span(&self, var: VariableIdx) -> SourceSpan {
        self.declarations.map[var].span()
    }
    pub fn var_name(&self, var: VariableIdx) -> Name {
        self.declarations.map[var].name()
    }

    pub fn ty_table(&self) -> Arc<TypeTable> {
        Arc::clone(self.ty_table.as_ref().expect("TypeTable was not yet built"))
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Named {
    Variable(VariableIdx),
    StructField(StructField),
}
impl TypeProvider for ItemContext {
    fn ty_data(&self, ty: TypeId) -> TypeData {
        self.ty_table.as_ref().expect("TypeTable was not yet set").ty_data(ty)
    }
    fn fields_of(&self, adt: Adt) -> Vec<AdtField> {
        self.ty_table.as_ref().expect("TypeTable was not yet set").fields_of(adt)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Trace<IDX: IdxWrap, V> {
    pub arena: IdxArena<IDX>,
    pub map: IdxMap<IDX, V>,
}

impl<IDX: IdxWrap, V> Trace<IDX, V> {
    pub fn new() -> Self {
        Trace { arena: Default::default(), map: Default::default() }
    }

    pub fn alloc(&mut self, value: V, data: IDX::Inner) -> IDX {
        let id = self.arena.alloc(data);
        self.map.insert(id, value);
        id
    }
}
impl<IDX: IdxWrap, V> Default for Trace<IDX, V> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SpanOrAstPtr<T: mist_syntax::AstNode> {
    Span(SourceSpan),
    Ptr(AstPtr<T>),
}

impl<T: mist_syntax::AstNode> SpanOrAstPtr<T> {
    #[allow(unused)]
    pub fn into_ptr(self) -> Option<AstPtr<T>> {
        match self {
            SpanOrAstPtr::Ptr(ptr) => Some(ptr),
            SpanOrAstPtr::Span(_) => None,
        }
    }
}
impl<T: mist_syntax::AstNode> Spanned for &'_ SpanOrAstPtr<T> {
    fn span(self) -> SourceSpan {
        match self {
            SpanOrAstPtr::Ptr(ptr) => ptr.span(),
            SpanOrAstPtr::Span(span) => *span,
        }
    }
}
impl<T: mist_syntax::AstNode> From<SourceSpan> for SpanOrAstPtr<T> {
    fn from(span: SourceSpan) -> Self {
        SpanOrAstPtr::Span(span)
    }
}
impl<T: mist_syntax::AstNode> From<&'_ T> for SpanOrAstPtr<T> {
    fn from(value: &T) -> Self {
        SpanOrAstPtr::Ptr(AstPtr::new(value))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionContext {
    pub(super) function_var: VariableIdx,
    pub(super) conditions: Vec<Condition>,
    pub(super) decreases: Decreases,
    pub(super) return_ty_src: Option<TypeSrc>,
}

impl FunctionContext {
    pub fn function_var(&self) -> VariableIdx {
        self.function_var
    }
    pub fn conditions(&self) -> &[Condition] {
        self.conditions.as_ref()
    }
    pub fn decreases(&self) -> Decreases {
        self.decreases
    }

    pub fn return_ty_src(&self) -> Option<TypeSrc> {
        self.return_ty_src
    }
}
