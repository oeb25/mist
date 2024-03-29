use std::collections::BTreeMap;

use crate::util::IdxMap;

use super::{
    unification::AdtInstantiation, Adt, AdtField, AdtKind, AdtPrototype, TypeData, TypeDataIdx,
    TypeId, TypeProvider,
};

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct TypeTable {
    type_data: IdxMap<TypeDataIdx, TypeData>,
    adt_prototypes: BTreeMap<AdtKind, AdtPrototype>,
    adt_instantiations: BTreeMap<Adt, AdtInstantiation>,
}

impl TypeTable {
    pub fn new(
        type_data: impl IntoIterator<Item = (TypeId, TypeData)>,
        adt_prototypes: impl IntoIterator<Item = (AdtKind, AdtPrototype)>,
        adt_instantiations: impl IntoIterator<Item = (Adt, AdtInstantiation)>,
    ) -> Self {
        Self {
            type_data: type_data.into_iter().map(|(ty, td)| (ty.data_idx(), td)).collect(),
            adt_prototypes: adt_prototypes.into_iter().collect(),
            adt_instantiations: adt_instantiations.into_iter().collect(),
        }
    }

    pub fn contains_ty(&self, ty: TypeId) -> bool {
        self.type_data.contains_idx(ty.data_idx())
    }

    pub fn adt_prototype(&self, adt_kind: AdtKind) -> Option<&AdtPrototype> {
        self.adt_prototypes.get(&adt_kind)
    }
    pub fn adts(&self) -> impl Iterator<Item = Adt> + '_ {
        self.adt_instantiations.keys().copied()
    }
    pub fn adt_instantiations(&self) -> impl Iterator<Item = &AdtInstantiation> {
        self.adt_instantiations.values()
    }
}

impl TypeProvider for TypeTable {
    fn ty_data(&self, ty: TypeId) -> TypeData {
        self.type_data[ty.data_idx()].clone()
    }
    fn adt_ty(&self, adt: Adt) -> Option<TypeId> {
        Some(self.adt_instantiations.get(&adt)?.ty)
    }
    fn fields_of(&self, adt: Adt) -> Vec<AdtField> {
        match adt.kind() {
            super::AdtKind::Struct(_, _) => self.adt_instantiations[&adt].fields.clone(),
            super::AdtKind::Enum => Vec::new(),
        }
    }
}
