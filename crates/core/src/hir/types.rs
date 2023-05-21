use std::collections::BTreeMap;

use crate::util::IdxMap;

use super::{Field, Struct, TypeData, TypeDataIdx, TypeId};

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
            type_data: type_data.into_iter().map(|(ty, td)| (ty.0, td)).collect(),
            field_types: field_types.into_iter().collect(),
        }
    }

    pub fn contains_ty(&self, ty: TypeId) -> bool {
        self.type_data.contains_idx(ty.0)
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct TypePtr<'a, T> {
    id: TypeId,
    table: &'a T,
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
        self[f].wrap(self)
    }

    fn ty_data(&self, ty: TypeId) -> TypeData<TypePtr<Self>> {
        self.type_data[ty.0].map(|id| id.wrap(self))
    }
}

impl std::ops::Index<Field> for TypeTable {
    type Output = TypeId;

    fn index(&self, field: Field) -> &Self::Output {
        &self.field_types[&field]
    }
}
