use mist_syntax::ast::AttrFlags;

use crate::{
    def::Name,
    hir::{typecheck::TypingMut, Param, TypeSrc},
};

use super::{primitive, GenericArgs, TypeId, TypeProvider, TDK};

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
    Range(T, RangeField),
}
impl<T> BuiltinField<T> {
    pub fn is_function(&self) -> bool {
        match self {
            BuiltinField::List(_, lf) => match lf {
                ListField::Len => false,
                ListField::ToSet => true,
            },
            BuiltinField::Set(_, sf) => match sf {
                SetField::Contains
                | SetField::Union
                | SetField::Intersection
                | SetField::ToList => true,
                SetField::Cardinality => false,
            },
            BuiltinField::MultiSet(_, sf) => match sf {
                MultiSetField::Cardinality => false,
            },
            BuiltinField::Range(_, sf) => match sf {
                RangeField::Min | RangeField::Max => false,
            },
        }
    }
    pub fn name(&self) -> Name {
        match self {
            BuiltinField::List(_, lf) => match lf {
                ListField::Len => Name::new("len"),
                ListField::ToSet => Name::new("to_set"),
            },
            BuiltinField::Set(_, sf) => match sf {
                SetField::Cardinality => Name::new("cardinality"),
                SetField::Contains => Name::new("contains"),
                SetField::Union => Name::new("union"),
                SetField::Intersection => Name::new("intersection"),
                SetField::ToList => Name::new("to_list"),
            },
            BuiltinField::MultiSet(_, sf) => match sf {
                MultiSetField::Cardinality => Name::new("cardinality"),
            },
            BuiltinField::Range(_, sf) => match sf {
                RangeField::Min => Name::new("min"),
                RangeField::Max => Name::new("max"),
            },
        }
    }
    pub fn is_ghost(&self) -> bool {
        match self {
            BuiltinField::List(_, lf) => match lf {
                ListField::Len => false,
                ListField::ToSet => false,
            },
            BuiltinField::Set(_, lf) => match lf {
                SetField::Cardinality => false,
                SetField::Contains => false,
                SetField::Union => false,
                SetField::Intersection => false,
                SetField::ToList => false,
            },
            BuiltinField::MultiSet(_, lf) => match lf {
                MultiSetField::Cardinality => false,
            },
            BuiltinField::Range(_, lf) => match lf {
                RangeField::Min | RangeField::Max => false,
            },
        }
    }
    pub(crate) fn map<S>(&self, mut f: impl FnMut(&T) -> S) -> BuiltinField<S> {
        match self {
            BuiltinField::List(t, lf) => BuiltinField::List(f(t), *lf),
            BuiltinField::Set(t, lf) => BuiltinField::Set(f(t), *lf),
            BuiltinField::MultiSet(t, lf) => BuiltinField::MultiSet(f(t), *lf),
            BuiltinField::Range(t, lf) => BuiltinField::Range(f(t), *lf),
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
                "contains" => Some(BuiltinField::Set(parent, SetField::Contains)),
                "union" => Some(BuiltinField::Set(parent, SetField::Union)),
                "intersection" => Some(BuiltinField::Set(parent, SetField::Intersection)),
                "to_list" => Some(BuiltinField::Set(parent, SetField::ToList)),
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
                "to_set" => Some(BuiltinField::List(parent, ListField::ToSet)),
                _ => None,
            },
            BuiltinKind::Range => match name {
                "min" => Some(BuiltinField::Range(parent, RangeField::Min)),
                "max" => Some(BuiltinField::Range(parent, RangeField::Max)),
                _ => None,
            },
        }
    }
    pub(crate) fn ty(self, tm: &mut impl TypingMut) -> TypeId {
        match self {
            BuiltinField::List(list_ty, lf) => match lf {
                ListField::Len => primitive::int(),
                ListField::ToSet => {
                    let elem_ty = match tm.ty_kind(list_ty) {
                        TDK::Builtin(_, args) => {
                            args.args(tm.db()).first().copied().unwrap_or(primitive::error())
                        }
                        _ => primitive::error(),
                    };
                    let set_ty = tm.alloc_ty_data(
                        TDK::Builtin(BuiltinKind::Set, GenericArgs::new(tm.db(), vec![elem_ty]))
                            .into(),
                    );
                    tm.alloc_ty_data(
                        TDK::Function {
                            attrs: AttrFlags::PURE,
                            name: Some(Name::new("to_set")),
                            params: Vec::new(),
                            return_ty: set_ty,
                        }
                        .into(),
                    )
                }
            },
            BuiltinField::Set(set_ty, lf) => {
                let elem_ty = match tm.ty_kind(set_ty) {
                    TDK::Builtin(_, args) => {
                        args.args(tm.db()).first().copied().unwrap_or(primitive::error())
                    }
                    _ => primitive::error(),
                };
                match lf {
                    SetField::Cardinality => primitive::int(),
                    SetField::Contains => {
                        let param = Param {
                            is_ghost: false,
                            name: Name::new("element"),
                            ty: tm.alloc_ty_src(TypeSrc::new(tm.db(), None, elem_ty), None),
                        };
                        tm.alloc_ty_data(
                            TDK::Function {
                                attrs: AttrFlags::PURE,
                                name: Some(Name::new("contains")),
                                params: vec![param],
                                return_ty: primitive::bool(),
                            }
                            .into(),
                        )
                    }
                    SetField::Union => {
                        let param = Param {
                            is_ghost: false,
                            name: Name::new("other"),
                            ty: tm.alloc_ty_src(TypeSrc::new(tm.db(), None, set_ty), None),
                        };
                        tm.alloc_ty_data(
                            TDK::Function {
                                attrs: AttrFlags::PURE,
                                name: Some(Name::new("union")),
                                params: vec![param],
                                return_ty: set_ty,
                            }
                            .into(),
                        )
                    }
                    SetField::Intersection => {
                        let param = Param {
                            is_ghost: false,
                            name: Name::new("other"),
                            ty: tm.alloc_ty_src(TypeSrc::new(tm.db(), None, set_ty), None),
                        };
                        tm.alloc_ty_data(
                            TDK::Function {
                                attrs: AttrFlags::PURE,
                                name: Some(Name::new("intersection")),
                                params: vec![param],
                                return_ty: set_ty,
                            }
                            .into(),
                        )
                    }
                    SetField::ToList => {
                        let list_ty = tm.alloc_ty_data(
                            TDK::Builtin(
                                BuiltinKind::List,
                                GenericArgs::new(tm.db(), vec![elem_ty]),
                            )
                            .into(),
                        );
                        tm.alloc_ty_data(
                            TDK::Function {
                                attrs: AttrFlags::PURE,
                                name: Some(Name::new("to_list")),
                                params: Vec::new(),
                                return_ty: list_ty,
                            }
                            .into(),
                        )
                    }
                }
            }
            BuiltinField::MultiSet(_, lf) => match lf {
                MultiSetField::Cardinality => primitive::int(),
            },
            BuiltinField::Range(_, lf) => match lf {
                RangeField::Min | RangeField::Max => primitive::int(),
            },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SetField {
    Cardinality,
    Contains,
    Union,
    Intersection,
    ToList,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MultiSetField {
    Cardinality,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ListField {
    Len,
    ToSet,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RangeField {
    Min,
    Max,
}
