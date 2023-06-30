use super::{Adt, AdtField, TypeData, TypeId, TDK};

pub trait TypeProvider: Sized {
    fn ty_data(&self, ty: TypeId) -> TypeData;
    fn adt_ty(&self, adt: Adt) -> Option<TypeId>;
    fn fields_of(&self, adt: Adt) -> Vec<AdtField>;

    fn ty_kind(&self, ty: TypeId) -> TDK<TypeId> {
        self.ty_data(ty).kind
    }
}
