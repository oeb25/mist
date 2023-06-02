use crate::def::StructField;

use super::{builtin, Field, ListField, TypeData, TypeDataPtr, TypeId, TypePtr, TDK};

pub trait TypeProvider: Sized {
    fn ty_data(&self, ty: TypeId) -> TypeData;
    fn struct_field_ty(&self, f: StructField) -> TypeId;

    fn field_ty(&self, f: Field) -> TypeId {
        match f {
            Field::StructField(sf) => self.struct_field_ty(sf),
            Field::List(_, ListField::Len) => builtin::int(),
            Field::Undefined => builtin::error(),
        }
    }
    fn field_ty_ptr(&self, f: Field) -> TypePtr<Self> {
        self.field_ty(f).wrap(self)
    }
    fn ty_data_ptr(&self, ty: TypeId) -> TypeDataPtr<Self> {
        self.ty_data(ty).map(|id| id.wrap(self))
    }
    fn ty_ptr(&self, ty: TypeId) -> TypePtr<Self> {
        TypePtr { id: ty, table: self }
    }
    fn ty_kind(&self, ty: TypeId) -> TDK<TypeId> {
        self.ty_data(ty).kind
    }
}
