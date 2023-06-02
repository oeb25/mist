use std::collections::BTreeMap;

use crate::{def::StructField, util::IdxMap};

use super::{Field, TypeData, TypeDataIdx, TypeId, TypeProvider};

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

impl TypeProvider for TypeTable {
    fn ty_data(&self, ty: TypeId) -> TypeData {
        self.type_data[ty.data_idx()].clone()
    }

    fn struct_field_ty(&self, f: StructField) -> TypeId {
        self.field_types[&f.into()]
    }
}
