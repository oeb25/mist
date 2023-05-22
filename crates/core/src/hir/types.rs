use std::collections::BTreeMap;

use crate::util::IdxMap;

use crate::hir::{Field, Struct, TypeData, TypeDataIdx, TypeId};

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct TypeTable {
    type_data: IdxMap<TypeDataIdx, TypeData>,
    field_types: BTreeMap<Field, TypeId>,
}

impl TypeTable {
    pub fn new(
        type_data: impl IntoIterator<Item = (TypeId, TypeData)>,
        field_types: impl IntoIterator<Item = (Field, TypeId)>,
    ) -> Self {
        Self {
            type_data: type_data
                .into_iter()
                .map(|(ty, td)| (ty.data_idx(), td))
                .collect(),
            field_types: field_types.into_iter().collect(),
        }
    }

    pub fn contains_ty(&self, ty: TypeId) -> bool {
        self.type_data.contains_idx(ty.data_idx())
    }
}

#[derive(PartialEq, Eq, Hash)]
pub struct TypePtr<'a, T> {
    id: TypeId,
    table: &'a T,
}

impl<'a, T: std::fmt::Debug> std::fmt::Debug for TypePtr<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypePtr").field("id", &self.id).finish()
    }
}

impl<'a, T> Clone for TypePtr<'a, T> {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            table: self.table,
        }
    }
}
impl<'a, T> Copy for TypePtr<'a, T> {}

impl<'a, T> TypePtr<'a, T>
where
    T: TypeProvider,
{
    pub fn id(self) -> TypeId {
        self.id
    }
    pub fn data(self) -> TypeData<Self> {
        self.table.ty_data(self.id)
    }

    pub fn strip_ghost(self) -> TypePtr<'a, T> {
        match self.data() {
            TypeData::Ghost(inner) => inner,
            _ => self,
        }
    }

    pub fn ty_struct(self) -> Option<Struct> {
        match self.data() {
            TypeData::Struct(s) => Some(s),

            TypeData::Ghost(inner) => inner.ty_struct(),
            TypeData::Ref { inner, .. } => inner.ty_struct(),
            TypeData::Optional(inner) => inner.ty_struct(),

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

    pub fn is_void(&self) -> bool {
        self.data().is_void()
    }

    pub fn with_provider<'b, P>(&self, table: &'b P) -> TypePtr<'b, P> {
        TypePtr { id: self.id, table }
    }
}

impl<'a, T> From<TypePtr<'a, T>> for TypeId {
    fn from(value: TypePtr<'a, T>) -> Self {
        value.id
    }
}

impl TypeId {
    pub fn wrap<T>(self, table: &T) -> TypePtr<T> {
        TypePtr { id: self, table }
    }
}

pub type TypeDataPtr<'a, T> = TypeData<TypePtr<'a, T>>;

impl<'a, T> TypeDataPtr<'a, T> {
    pub fn with_provider<'b, P>(&self, p: &'b P) -> TypeDataPtr<'b, P> {
        self.map(|t| TypePtr { id: t.id, table: p })
    }
}

pub trait TypeProvider: Sized {
    fn field_ty(&self, f: Field) -> TypePtr<Self>;

    fn ty_data(&self, ty: TypeId) -> TypeDataPtr<Self>;

    fn ty(&self, ty: TypeId) -> TypePtr<Self> {
        TypePtr {
            id: ty,
            table: self,
        }
    }
}

impl TypeProvider for TypeTable {
    fn field_ty(&self, f: Field) -> TypePtr<Self> {
        if let Some(ty) = self.field_types.get(&f) {
            ty.wrap(self)
        } else {
            panic!("field '{f:?}' was not found in {self:?}")
        }
    }

    fn ty_data(&self, ty: TypeId) -> TypeData<TypePtr<Self>> {
        self.type_data[ty.data_idx()].map(|id| id.wrap(self))
    }
}
