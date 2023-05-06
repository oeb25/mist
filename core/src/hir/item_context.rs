use std::collections::HashMap;

use derive_new::new;
use mist_syntax::{
    ast::{self, Spanned},
    ptr::AstPtr,
    SourceSpan,
};

use crate::{
    util::{IdxArena, IdxMap, IdxWrap},
    VariableDeclaration,
};

use super::{
    Condition, Decreases, Expr, ExprIdx, Field, Ident, ItemId, Param, Struct, TypeData,
    TypeDataIdx, TypeId, TypeSrc, TypeSrcId, Variable, VariableIdx, VariableRef,
};

#[derive(new, Debug, Clone, PartialEq, Eq)]
pub struct ItemContext {
    pub(super) item_id: ItemId,
    #[new(default)]
    pub(super) function_context: Option<FunctionContext>,
    #[new(default)]
    pub(super) declarations: Trace<VariableIdx, VariableDeclaration>,
    #[new(default)]
    pub(super) var_types: IdxMap<VariableIdx, TypeSrcId>,
    #[new(default)]
    pub(super) expr_arena: IdxArena<ExprIdx>,
    #[new(default)]
    pub(super) ty_src_arena: IdxArena<TypeSrcId>,

    #[new(default)]
    pub(super) ty_table: IdxMap<TypeDataIdx, TypeData>,
    #[new(default)]
    pub(super) named_types: HashMap<String, TypeId>,
    #[new(default)]
    pub(super) structs: HashMap<Struct, Vec<(Field, TypeSrcId)>>,
    #[new(default)]
    pub(super) struct_types: HashMap<Struct, TypeSrcId>,

    #[new(default)]
    pub(super) params: Vec<Param<VariableIdx>>,
    #[new(default)]
    pub(super) body_expr: Option<ExprIdx>,
    #[new(default)]
    pub(super) return_ty: Option<TypeSrcId>,

    pub(super) error_ty: TypeId,
    pub(super) int_ty: TypeId,
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
impl std::ops::Index<TypeSrcId> for ItemContext {
    type Output = TypeSrc;

    fn index(&self, index: TypeSrcId) -> &Self::Output {
        &self.ty_src_arena[index]
    }
}
impl std::ops::Index<TypeId> for ItemContext {
    type Output = TypeData;

    fn index(&self, index: TypeId) -> &Self::Output {
        if self.ty_table.contains_idx(index.0) {
            &self.ty_table[index.0]
        } else {
            todo!("ItemContext::ty_table was missing key '{:?}'", index)
        }
    }
}
impl ItemContext {
    pub fn item_id(&self) -> ItemId {
        self.item_id
    }
    pub fn function_context(&self) -> Option<&FunctionContext> {
        self.function_context.as_ref()
    }
    pub fn function_var(&self) -> Option<VariableRef> {
        self.function_context.as_ref().map(|cx| cx.function_var)
    }
    pub fn conditions(&self) -> impl Iterator<Item = &Condition> {
        self.function_context.iter().flat_map(|cx| &cx.conditions)
    }
    pub fn params(&self) -> &[Param<VariableIdx>] {
        &self.params
    }
    pub fn return_ty(&self) -> Option<TypeId> {
        self.return_ty.map(|ty| self[ty].ty)
    }
    pub fn body_expr(&self) -> Option<ExprIdx> {
        self.body_expr
    }
    pub fn var_ty_src(&self, var: impl Into<VariableIdx>) -> TypeSrcId {
        self.var_types[var.into()]
    }
    pub fn var_ty(&self, var: impl Into<VariableIdx>) -> TypeId {
        self[self.var_types[var.into()]].ty
    }
    pub fn expr(&self, expr: ExprIdx) -> &Expr {
        &self.expr_arena[expr]
    }
    pub fn expr_ty(&self, expr: ExprIdx) -> TypeId {
        self.expr_arena[expr].ty
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
        self.declarations.map[var.into()].name()
    }
    pub fn field_ty(&self, field: &Field) -> TypeId {
        match &field.parent {
            super::FieldParent::Struct(s) => self.structs[s]
                .iter()
                .find_map(|(f, ty)| if f == field { Some(self[*ty].ty) } else { None })
                .unwrap(),
            super::FieldParent::List(_) => match field.name.as_str() {
                "len" => self.int_ty(),
                _ => todo!(),
            },
        }
    }
    pub fn field_ty_src(&self, field: &Field) -> Option<TypeSrcId> {
        match &field.parent {
            super::FieldParent::Struct(s) => {
                self.structs[s]
                    .iter()
                    .find_map(|(f, ty)| if f == field { Some(*ty) } else { None })
            }
            super::FieldParent::List(_) => match field.name.as_str() {
                "len" => None,
                _ => todo!(),
            },
        }
    }
    pub fn struct_ty(&self, s: Struct) -> TypeSrcId {
        self.struct_types[&s]
    }
    pub fn error_ty(&self) -> TypeId {
        self.error_ty
    }
    pub fn int_ty(&self) -> TypeId {
        self.int_ty
    }

    pub fn ty_data(&self, index: TypeId) -> &TypeData {
        &self.ty_table[index.0]
    }

    pub(crate) fn ty_data_without_ghost(&self, ty: TypeId) -> &TypeData {
        match self.ty_data(ty) {
            TypeData::Ghost(inner) => self.ty_data_without_ghost(*inner),
            td => td,
        }
    }
    pub fn ty_struct(&self, ty: TypeId) -> Option<Struct> {
        match self.ty_data(ty) {
            TypeData::Struct(s) => Some(*s),

            TypeData::Ghost(inner) => self.ty_struct(*inner),
            TypeData::Ref { inner, .. } => self.ty_struct(*inner),
            TypeData::Optional(inner) => self.ty_struct(*inner),

            TypeData::Error
            | TypeData::Void
            | TypeData::List(_)
            | TypeData::Primitive(_)
            | TypeData::Null
            | TypeData::Function { .. }
            | TypeData::Range(_)
            | TypeData::Free => None,
        }
    }
}

impl TypeId {
    pub fn strip_ghost(self, cx: &ItemContext) -> TypeId {
        match cx[self] {
            TypeData::Ghost(inner) => inner,
            _ => self,
        }
    }
    pub fn is_ghost(self, cx: &ItemContext) -> bool {
        matches!(cx[self], TypeData::Ghost(_))
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ItemSourceMap {
    pub(super) expr_map: HashMap<SpanOrAstPtr<ast::Expr>, ExprIdx>,
    pub(super) expr_map_back: IdxMap<ExprIdx, SpanOrAstPtr<ast::Expr>>,
    pub(super) ty_src_map: IdxMap<TypeSrcId, SpanOrAstPtr<ast::Type>>,
    pub(super) ty_src_map_back: HashMap<SpanOrAstPtr<ast::Type>, TypeSrcId>,
}

impl ItemSourceMap {
    pub fn expr_span(&self, expr: ExprIdx) -> SourceSpan {
        self.expr_map_back[expr].span()
    }
}

impl std::ops::Index<ExprIdx> for ItemSourceMap {
    type Output = SpanOrAstPtr<ast::Expr>;

    fn index(&self, index: ExprIdx) -> &Self::Output {
        &self.expr_map_back[index]
    }
}
impl std::ops::Index<TypeSrcId> for ItemSourceMap {
    type Output = SpanOrAstPtr<ast::Type>;

    fn index(&self, index: TypeSrcId) -> &Self::Output {
        &self.ty_src_map[index]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(super) struct Trace<IDX: IdxWrap, V> {
    pub arena: IdxArena<IDX>,
    pub map: IdxMap<IDX, V>,
}

impl<IDX: IdxWrap, V> Trace<IDX, V> {
    pub fn new() -> Self {
        Trace {
            arena: Default::default(),
            map: Default::default(),
        }
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
    pub(super) function_var: VariableRef,
    pub(super) conditions: Vec<Condition>,
    pub(super) decreases: Decreases,
    pub(super) return_ty_src: Option<TypeSrcId>,
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

    pub fn return_ty_src(&self) -> Option<TypeSrcId> {
        self.return_ty_src
    }
}
