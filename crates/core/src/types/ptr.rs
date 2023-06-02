use crate::def::Struct;

use super::{TypeData, TypeId, TypeProvider, TDK};

#[derive(PartialEq, Eq, Hash)]
pub struct TypePtr<'a, T> {
    pub(super) id: TypeId,
    pub(super) table: &'a T,
}

impl<'a, T: std::fmt::Debug> std::fmt::Debug for TypePtr<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypePtr").field("id", &self.id).finish()
    }
}

impl<'a, T> Clone for TypePtr<'a, T> {
    fn clone(&self) -> Self {
        Self { id: self.id, table: self.table }
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
        self.table.ty_data_ptr(self.id)
    }
    pub fn kind(self) -> TDK<Self> {
        self.data().kind
    }
    pub fn ty_struct(self) -> Option<Struct> {
        match self.kind() {
            TDK::Struct(s) => Some(s),

            TDK::Ref { inner, .. } => inner.ty_struct(),
            TDK::Optional(inner) => inner.ty_struct(),

            TDK::Error
            | TDK::Void
            | TDK::List(_)
            | TDK::Primitive(_)
            | TDK::Null
            | TDK::Function { .. }
            | TDK::Range(_)
            | TDK::Free => None,
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
