use std::{collections::HashMap, sync::Mutex};

use ena::unify::InPlaceUnificationTable;

use crate::{
    hir::{Primitive, TypeData, TypeDataIdx, TypeId},
    util::IdxWrap,
};

pub struct Typer {
    ty_table: Mutex<InPlaceUnificationTable<TypeId>>,
    ty_cache: HashMap<TypeData, TypeId>,
    ty_keys: Vec<TypeId>,
}

macro_rules! type_prelude {
    ($($id:literal => ($fn_name:ident, $td:expr),)*) => {
        pub mod builtin {
            use super::*;

            $(
                pub fn $fn_name() -> TypeId {
                    TypeId(TypeDataIdx::from_raw($id.into()))
                }
            )*
        }
        use builtin::*;
        fn init_ty_table() -> InPlaceUnificationTable<TypeId> {
            let mut ty_table = InPlaceUnificationTable::default();

            $(
                assert_eq!(
                    ty_table.new_key($td),
                    $fn_name()
                );
            )*

            ty_table
        }

        impl Typer {
            pub fn new() -> Typer {
                let ty_cache = [$(($td, $fn_name())),*].into_iter().collect();
                let ty_keys = vec![$($fn_name()),*];

                Typer {
                    ty_table: Mutex::new(init_ty_table()),
                    ty_cache,
                    ty_keys,
                }
            }
        }
    };
}

type_prelude! {
    0 => (bool, TypeData::Primitive(Primitive::Bool)),
    1 => (ghost_bool, TypeData::Ghost(bool())),
    2 => (int, TypeData::Primitive(Primitive::Int)),
    3 => (void, TypeData::Void),
    4 => (null, TypeData::Null),
    5 => (error, TypeData::Error),
}

impl Typer {
    pub fn new_free(&mut self) -> TypeId {
        let key = self.ty_table.lock().unwrap().new_key(TypeData::Free);
        self.ty_keys.push(key);
        key
    }
    pub fn ty_id(&mut self, data: TypeData) -> TypeId {
        let key = *self.ty_cache.entry(data).or_insert_with_key(|td| {
            let key = self.ty_table.lock().unwrap().new_key(td.clone());
            self.ty_keys.push(key);
            key
        });
        key
    }
    pub fn probe_type(&self, ty: TypeId) -> TypeData {
        self.ty_table.lock().unwrap().inlined_probe_value(ty)
    }
    pub fn canonicalized(&self) -> impl Iterator<Item = (TypeId, TypeData)> + '_ {
        self.ty_keys.iter().map(move |&ty| {
            let td = self.ty_table.lock().unwrap().probe_value(ty);
            (ty, td)
        })
    }

    fn ghost(&mut self, t: TypeId) -> TypeId {
        self.ty_id(TypeData::Ghost(t))
    }

    pub fn unify(&mut self, expected: TypeId, actual: TypeId) -> Option<TypeId> {
        {
            let expected_no_ghost = expected.tc_strip_ghost(self);
            let actual_no_ghost = actual.tc_strip_ghost(self);
            if self.probe_type(expected_no_ghost).is_void()
                && self.probe_type(actual_no_ghost).is_void()
            {
                return Some(expected);
            }
        }

        Some(match (self.probe_type(expected), self.probe_type(actual)) {
            (TypeData::Error, _) | (_, TypeData::Error) => expected,
            (TypeData::Void, TypeData::Void) => expected,
            (
                TypeData::Ref {
                    is_mut: mut1,
                    inner: inner1,
                },
                TypeData::Ref {
                    is_mut: mut2,
                    inner: inner2,
                },
            ) => {
                let inner = self.unify(inner1, inner2)?;
                self.ty_id(TypeData::Ref {
                    is_mut: mut1 && mut2,
                    inner,
                })
            }
            (TypeData::Optional(inner1), TypeData::Optional(inner2)) => {
                self.unify(inner1, inner2)?;
                expected
            }
            (TypeData::Optional(inner), TypeData::Struct(_)) if inner == actual => expected,
            (TypeData::Struct(_), TypeData::Optional(inner)) if inner == expected => actual,
            (TypeData::Primitive(p1), TypeData::Primitive(p2)) if p1 == p2 => expected,
            (TypeData::Struct(s1), TypeData::Struct(s2)) if s1 == s2 => expected,
            (TypeData::List(s1), TypeData::List(s2)) => {
                self.unify(s1, s2)?;
                expected
            }
            (TypeData::Null, TypeData::Null) => expected,
            (TypeData::Null, TypeData::Optional(_)) => actual,
            (TypeData::Optional(_), TypeData::Null) => expected,

            // Ghost
            (TypeData::Ghost(t1), TypeData::Ghost(t2)) => {
                if let Some(t) = self.unify(t1, t2) {
                    self.ghost(t)
                } else {
                    return None;
                }
            }
            (TypeData::Ghost(t1), _) => {
                if let Some(t) = self.unify(t1, actual) {
                    self.ghost(t)
                } else {
                    return None;
                }
            }
            (TypeData::Free, _) | (_, TypeData::Free) => {
                self.ty_table
                    .lock()
                    .unwrap()
                    .unify_var_var(expected, actual)
                    .unwrap();
                expected
            }
            _ => return None,
        })
    }
}
