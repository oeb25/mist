use crate::def::Name;

use super::{primitive, TypeId, TypeProvider};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BuiltinKind {
    Set,
    MultiSet,
    Map,
    List,
    Range,
}

impl BuiltinKind {
    pub fn name(&self) -> Name {
        match self {
            BuiltinKind::Set => Name::new("Set"),
            BuiltinKind::MultiSet => Name::new("MultiSet"),
            BuiltinKind::Map => Name::new("Map"),
            BuiltinKind::List => Name::new("List"),
            BuiltinKind::Range => Name::new("Range"),
        }
    }

    pub fn parse(name: &str) -> Option<BuiltinKind> {
        Some(match name {
            "Set" => BuiltinKind::Set,
            "MultiSet" => BuiltinKind::MultiSet,
            "Map" => BuiltinKind::Map,
            "List" => BuiltinKind::Range,
            "Range" => BuiltinKind::Range,
            _ => return None,
        })
    }

    pub fn arity(&self) -> usize {
        match self {
            BuiltinKind::Set => 1,
            BuiltinKind::MultiSet => 1,
            BuiltinKind::Map => 2,
            BuiltinKind::List => 1,
            BuiltinKind::Range => 1,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BuiltinField<T> {
    List(T, ListField),
    Set(T, SetField),
    MultiSet(T, MultiSetField),
}
impl<T> BuiltinField<T> {
    pub fn name(&self) -> Name {
        match self {
            BuiltinField::List(_, lf) => match lf {
                ListField::Len => Name::new("len"),
            },
            BuiltinField::Set(_, sf) => match sf {
                SetField::Cardinality => Name::new("cardinality"),
            },
            BuiltinField::MultiSet(_, sf) => match sf {
                MultiSetField::Cardinality => Name::new("cardinality"),
            },
        }
    }
    pub fn is_ghost(&self) -> bool {
        match self {
            BuiltinField::List(_, lf) => match lf {
                ListField::Len => false,
            },
            BuiltinField::Set(_, lf) => match lf {
                SetField::Cardinality => false,
            },
            BuiltinField::MultiSet(_, lf) => match lf {
                MultiSetField::Cardinality => false,
            },
        }
    }
    pub(crate) fn map<S>(&self, mut f: impl FnMut(&T) -> S) -> BuiltinField<S> {
        match self {
            BuiltinField::List(t, lf) => BuiltinField::List(f(t), *lf),
            BuiltinField::Set(t, lf) => BuiltinField::Set(f(t), *lf),
            BuiltinField::MultiSet(t, lf) => BuiltinField::MultiSet(f(t), *lf),
        }
    }
}
impl BuiltinField<TypeId> {
    pub fn try_create(
        _tp: &impl TypeProvider,
        parent: TypeId,
        kind: BuiltinKind,
        name: &str,
    ) -> Option<BuiltinField<TypeId>> {
        #[allow(clippy::match_single_binding)]
        match kind {
            BuiltinKind::Set => match name {
                "cardinality" => Some(BuiltinField::Set(parent, SetField::Cardinality)),
                _ => None,
            },
            BuiltinKind::MultiSet => match name {
                "cardinality" => Some(BuiltinField::MultiSet(parent, MultiSetField::Cardinality)),
                _ => None,
            },
            BuiltinKind::Map => match name {
                _ => None,
            },
            BuiltinKind::List => match name {
                "len" => Some(BuiltinField::List(parent, ListField::Len)),
                _ => None,
            },
            BuiltinKind::Range => match name {
                _ => None,
            },
        }
    }
    pub fn ty(&self) -> TypeId {
        match self {
            BuiltinField::List(_, lf) => match lf {
                ListField::Len => primitive::int(),
            },
            BuiltinField::Set(_, lf) => match lf {
                SetField::Cardinality => primitive::int(),
            },
            BuiltinField::MultiSet(_, lf) => match lf {
                MultiSetField::Cardinality => primitive::int(),
            },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SetField {
    Cardinality,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MultiSetField {
    Cardinality,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ListField {
    Len,
}
