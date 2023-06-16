use std::{collections::HashMap, sync::Arc};

use derive_new::new;
use mist_syntax::{
    ast::{self, Spanned},
    ptr::AstPtr,
    SourceSpan,
};
use tracing::info;

use crate::{
    def::{Name, Struct, StructField},
    types::{Field, TypeData, TypeId, TypeProvider, TypePtr, TypeTable},
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
    pub(super) self_ty: Option<TypeSrc>,
    #[new(default)]
    pub(super) self_invariants: Vec<ExprIdx>,

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
        self.return_ty.map(|ty| ty.ty(db))
    }
    pub fn self_ty(&self, db: &dyn crate::Db) -> Option<TypeId> {
        self.self_ty.map(|ty| ty.ty(db))
    }
    pub fn self_invariants(&self) -> &[ExprIdx] {
        &self.self_invariants
    }
    pub fn body_expr(&self) -> Option<ExprIdx> {
        self.body_expr
    }
    pub fn var(&self, var: VariableIdx) -> Variable {
        self.declarations.arena[var]
    }
    pub fn var_ty(&self, db: &dyn crate::Db, var: VariableIdx) -> TypePtr<Self> {
        self.var(var).ty(db).wrap(self)
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
    pub fn expr_ty(&self, expr: ExprIdx) -> TypePtr<Self> {
        self.expr_arena[expr].ty.wrap(self)
    }
    pub fn decl(&self, var: VariableIdx) -> &VariableDeclaration {
        &self.declarations.map[var]
    }
    pub fn var_span(&self, var: VariableIdx) -> SourceSpan {
        self.declarations.map[var].span()
    }
    pub fn var_name(&self, var: VariableIdx) -> Name {
        self.declarations.map[var].name()
    }
    pub fn field_ty_src(&self, field: Field) -> Option<TypeSrc> {
        match field {
            Field::StructField(sf) => Some(self.file_context.struct_field_types[&sf]),
            Field::List(_, _) | Field::Undefined => None,
        }
    }
    pub fn struct_ty_src(&self, s: Struct) -> TypeSrc {
        self.file_context.struct_types[&s]
    }
    pub fn struct_ty(&self, db: &dyn crate::Db, s: Struct) -> TypePtr<Self> {
        self.struct_ty_src(s).ty(db).wrap(self)
    }

    pub fn ty_table(&self) -> Arc<TypeTable> {
        Arc::clone(self.ty_table.as_ref().expect("TypeTable was not yet built"))
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Named {
    Variable(VariableIdx),
}
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ItemSourceMap {
    name_map: HashMap<AstPtr<ast::NameOrNameRef>, Named>,
    name_map_back: HashMap<Named, Vec<AstPtr<ast::NameOrNameRef>>>,
    stmt_map: HashMap<AstPtr<ast::Stmt>, StatementId>,
    stmt_map_back: IdxMap<StatementId, AstPtr<ast::Stmt>>,
    expr_map: HashMap<SpanOrAstPtr<ast::Expr>, ExprIdx>,
    expr_map_back: IdxMap<ExprIdx, SpanOrAstPtr<ast::Expr>>,
    ty_src_map: HashMap<TypeSrc, SpanOrAstPtr<ast::Type>>,
    ty_src_map_back: HashMap<SpanOrAstPtr<ast::Type>, TypeSrc>,
}

impl TypeProvider for ItemContext {
    fn ty_data(&self, ty: TypeId) -> TypeData {
        self.ty_table.as_ref().expect("TypeTable was not yet set").ty_data(ty)
    }

    fn struct_field_ty(&self, f: StructField) -> TypeId {
        self.ty_table.as_ref().expect("TypeTable was not yet set").struct_field_ty(f)
    }
}

#[derive(Debug, Clone, thiserror::Error)]
pub enum ItemSourceMapError {
    #[error("entry '{key}' already had a mapping (value: '{value}', type: '{ty}')")]
    AlreadyPresent { ty: &'static str, key: String, value: String },
}

impl ItemSourceMap {
    pub fn register_name(
        &mut self,
        name: AstPtr<ast::NameOrNameRef>,
        named: Named,
    ) -> Result<(), ItemSourceMapError> {
        info!(?named, "registering named");

        let old = self.name_map.insert(name.clone(), named.clone());
        self.name_map_back.entry(named).or_default().push(name.clone());
        if let Some(old) = old {
            Err(ItemSourceMapError::AlreadyPresent {
                ty: "AstPtr<ast::NameOrNameRef>",
                key: format!("{name:?}"),
                value: format!("{old:?}"),
            })
        } else {
            Ok(())
        }
    }
    pub fn register_stmt(
        &mut self,
        ast: AstPtr<ast::Stmt>,
        stmt: StatementId,
    ) -> Result<(), ItemSourceMapError> {
        let old = self.stmt_map.insert(ast.clone(), stmt);
        let old = old.and_then(|old| (old != stmt).then_some(old));
        self.stmt_map_back.insert(stmt, ast);
        if let Some(old) = old {
            Err(ItemSourceMapError::AlreadyPresent {
                ty: "Stmt",
                key: format!("{stmt:?}"),
                value: format!("{old:?}"),
            })
        } else {
            Ok(())
        }
    }
    pub fn register_expr(
        &mut self,
        ast: SpanOrAstPtr<ast::Expr>,
        expr: ExprIdx,
    ) -> Result<(), ItemSourceMapError> {
        let old = self.expr_map.insert(ast.clone(), expr);
        let old = old.and_then(|old| (old != expr).then_some(old));
        self.expr_map_back.insert(expr, ast);
        if let Some(old) = old {
            Err(ItemSourceMapError::AlreadyPresent {
                ty: "Expr",
                key: format!("{expr:?}"),
                value: format!("{old:?}"),
            })
        } else {
            Ok(())
        }
    }
    pub fn register_ty_src(
        &mut self,
        ty_src: TypeSrc,
        ast: SpanOrAstPtr<ast::Type>,
    ) -> Result<(), ItemSourceMapError> {
        let old = self.ty_src_map.insert(ty_src, ast.clone());
        let old = old.and_then(|old| (old != ast).then_some(old));
        self.ty_src_map_back.insert(ast, ty_src);
        if let Some(old) = old {
            Err(ItemSourceMapError::AlreadyPresent {
                ty: "TypeSrc",
                key: format!("{ty_src:?}"),
                value: format!("{old:?}"),
            })
        } else {
            Ok(())
        }
    }
}

impl ItemSourceMap {
    pub fn expr_src(&self, cx: &ItemContext, expr: ExprIdx) -> SpanOrAstPtr<ast::Expr> {
        if let Some(&desugared) = cx.desugared_back.get(expr) {
            self.expr_map_back[desugared].clone()
        } else {
            self.expr_map_back[expr].clone()
        }
    }
    pub fn expr_span(&self, cx: &ItemContext, expr: ExprIdx) -> SourceSpan {
        if let Some(&desugared) = cx.desugared_back.get(expr) {
            self.expr_map_back[desugared].span()
        } else {
            self.expr_map_back[expr].span()
        }
    }
    pub fn name_var(&self, name: &AstPtr<ast::NameOrNameRef>) -> Option<Named> {
        self.name_map.get(name).cloned()
    }
    pub fn named_references<'a>(
        &'a self,
        named: &Named,
    ) -> impl Iterator<Item = &'a AstPtr<ast::NameOrNameRef>> {
        self.name_map_back.get(named).into_iter().flatten()
    }
    pub fn names(&self) -> impl Iterator<Item = (&AstPtr<ast::NameOrNameRef>, &Named)> {
        self.name_map.iter()
    }
    pub fn stmt_ast(&self, stmt: StatementId) -> Option<AstPtr<ast::Stmt>> {
        self.stmt_map_back.get(stmt).cloned()
    }
    pub fn ty_ast(&self, ast: SpanOrAstPtr<ast::Type>) -> Option<TypeSrc> {
        self.ty_src_map_back.get(&ast).copied()
    }
}

impl std::ops::Index<ExprIdx> for ItemSourceMap {
    type Output = SpanOrAstPtr<ast::Expr>;

    fn index(&self, index: ExprIdx) -> &Self::Output {
        &self.expr_map_back[index]
    }
}
impl std::ops::Index<TypeSrc> for ItemSourceMap {
    type Output = SpanOrAstPtr<ast::Type>;

    fn index(&self, index: TypeSrc) -> &Self::Output {
        &self.ty_src_map[&index]
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
