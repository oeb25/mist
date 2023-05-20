use crate::util::IdxMap;

use super::{TypeData, TypeDataIdx, TypeId};

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct TypeTable(IdxMap<TypeDataIdx, TypeData>);

impl TypeTable {
    pub fn contains_ty(&self, ty: TypeId) -> bool {
        self.0.contains_idx(ty.0)
    }
}

impl FromIterator<(TypeId, TypeData)> for TypeTable {
    fn from_iter<T: IntoIterator<Item = (TypeId, TypeData)>>(iter: T) -> Self {
        TypeTable(iter.into_iter().map(|(ty, td)| (ty.0, td)).collect())
    }
}

trait TypeProvider {
    fn ty_data(&self, ty: TypeId) -> &TypeData;
}

impl TypeProvider for TypeTable {
    fn ty_data(&self, ty: TypeId) -> &TypeData {
        &self[ty]
    }
}

impl std::ops::Index<TypeId> for TypeTable {
    type Output = TypeData;

    fn index(&self, ty: TypeId) -> &Self::Output {
        &self.0[ty.0]
    }
}
