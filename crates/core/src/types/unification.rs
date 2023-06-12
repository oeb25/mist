use std::{collections::HashMap, sync::Mutex};

use ena::unify::InPlaceUnificationTable;

use crate::util::IdxWrap;

use super::{data::Primitive, TypeData, TypeDataIdx, TDK};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(TypeDataIdx);

impl TypeId {
    pub fn data_idx(self) -> TypeDataIdx {
        self.0
    }
}

impl PartialOrd for TypeId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.0.into_raw().partial_cmp(&other.0.into_raw())
    }
}
impl Ord for TypeId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.into_raw().cmp(&other.0.into_raw())
    }
}

impl ena::unify::UnifyKey for TypeId {
    type Value = TypeData;

    fn index(&self) -> u32 {
        self.0.into_raw().into()
    }

    fn from_index(u: u32) -> Self {
        Self(TypeDataIdx::from_raw(u.into()))
    }

    fn tag() -> &'static str {
        "TypeId"
    }
}

#[derive(Debug)]
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
                    ty_table.new_key($td.into()),
                    $fn_name()
                );
            )*

            ty_table
        }

        impl Typer {
            pub fn new() -> Typer {
                let ty_cache = [$(($td.into(), $fn_name())),*].into_iter().collect();
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

impl Default for Typer {
    fn default() -> Typer {
        Typer::new()
    }
}

type_prelude! {
    0 => (bool, TDK::Primitive(Primitive::Bool)),
    1 => (ghost_bool, TDK::Primitive(Primitive::Bool).ghost()),
    2 => (int, TDK::Primitive(Primitive::Int)),
    3 => (ghost_int, TDK::Primitive(Primitive::Int).ghost()),
    4 => (void, TDK::Void),
    5 => (null, TDK::Null),
    6 => (error, TDK::Error),
}

impl Typer {
    pub fn new_free(&mut self) -> TypeId {
        let key = self.ty_table.lock().unwrap().new_key(TDK::Free.into());
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

    pub fn unify(&mut self, expected: TypeId, actual: TypeId) -> Option<TypeId> {
        if self.probe_type(expected).is_void() && self.probe_type(actual).is_void() {
            return Some(expected);
        }

        let t1 = self.probe_type(expected);
        let t2 = self.probe_type(actual);

        if !t1.is_ghost && t2.is_ghost {
            // NOTE: Ghost in place where non-ghost is expected
            if t1.kind != TDK::Free {
                return None;
            }
        }

        let res = match (t1.kind, t2.kind) {
            (TDK::Error, _) | (_, TDK::Error) => expected,
            (TDK::Void, TDK::Void) => expected,
            (
                TDK::Ref { is_mut: mut1, inner: inner1 },
                TDK::Ref { is_mut: mut2, inner: inner2 },
            ) => {
                let inner = self.unify(inner1, inner2)?;
                self.ty_id(TDK::Ref { is_mut: mut1 && mut2, inner }.into())
            }
            (TDK::Optional(inner1), TDK::Optional(inner2)) => {
                self.unify(inner1, inner2)?;
                expected
            }
            (TDK::Optional(inner), TDK::Struct(_)) if inner == actual => expected,
            (TDK::Struct(_), TDK::Optional(inner)) if inner == expected => actual,
            (TDK::Range(inner1), TDK::Range(inner2)) => {
                self.unify(inner1, inner2)?;
                expected
            }
            (TDK::Primitive(p1), TDK::Primitive(p2)) if p1 == p2 => expected,
            (TDK::Struct(s1), TDK::Struct(s2)) if s1 == s2 => expected,
            (TDK::List(s1), TDK::List(s2)) => {
                self.unify(s1, s2)?;
                expected
            }
            (TDK::Null, TDK::Null) => expected,
            (TDK::Null, TDK::Optional(_)) => actual,
            (TDK::Optional(_), TDK::Null) => expected,
            (TDK::Free, _) | (_, TDK::Free) => {
                self.ty_table.lock().unwrap().unify_var_var(expected, actual).unwrap();
                expected
            }
            _ => return None,
        };

        // TODO: should we ghostify res?
        Some(res)
    }
}
