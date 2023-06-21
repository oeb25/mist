use super::{primitive, Adt, AdtField, Field, TypeData, TypeDataPtr, TypeId, TypePtr, TDK};

pub trait TypeProvider: Sized {
    fn ty_data(&self, ty: TypeId) -> TypeData;
    fn fields_of(&self, adt: Adt) -> Vec<AdtField>;

    fn field_ty(&self, f: Field) -> TypeId {
        match f {
            Field::AdtField(af) => af.ty(),
            Field::Builtin(bf) => bf.ty(),
            Field::Undefined => primitive::error(),
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
