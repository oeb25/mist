use std::{collections::HashMap, sync::Mutex};

use ena::unify::InPlaceUnificationTable;
use indexmap::IndexMap;
use itertools::Itertools;
use tracing::{debug, info};

use crate::{def::Generic, util::IdxWrap};

use super::{
    data::Primitive, Adt, AdtField, AdtKind, AdtPrototype, GenericArgs, StructPrototype, TypeData,
    TypeDataIdx, TDK,
};

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AdtInstantiation {
    pub adt: Adt,
    pub ty: TypeId,
    pub fields: Vec<AdtField>,
}

#[derive(Debug, Default)]
pub struct AdtPrototypes {
    data: IndexMap<AdtKind, AdtPrototype>,
}

impl AdtPrototypes {
    fn insert(&mut self, kind: AdtKind, prototype: AdtPrototype) -> Option<AdtPrototype> {
        match kind {
            AdtKind::Struct(_, _) => self.data.insert(kind, prototype),
            AdtKind::Enum => todo!(),
        }
    }

    fn get(&self, kind: AdtKind) -> Option<AdtPrototype> {
        match kind {
            AdtKind::Struct(_, _) => self.data.get(&kind).cloned(),
            AdtKind::Enum => todo!(),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (AdtKind, &AdtPrototype)> {
        self.data.iter().map(|(k, v)| (*k, v))
    }
}

#[derive(Debug)]
pub struct Typer {
    ty_table: Mutex<InPlaceUnificationTable<TypeId>>,
    ty_cache: HashMap<TypeData, TypeId>,
    ty_keys: Vec<TypeId>,
    adt_prototypes: AdtPrototypes,
    adt_tys: IndexMap<Adt, TypeId>,
    adt_instantiations: IndexMap<Adt, AdtInstantiation>,
}

macro_rules! type_prelude {
    ($($id:literal => ($fn_name:ident, $td:expr),)*) => {
        pub mod primitive {
            use super::*;

            $(
                pub fn $fn_name() -> TypeId {
                    TypeId(TypeDataIdx::from_raw($id.into()))
                }
            )*
        }
        use primitive::*;
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
                    adt_prototypes: Default::default(),
                    adt_tys: Default::default(),
                    adt_instantiations: Default::default(),
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
    pub fn new_generic(&mut self, generic: Generic) -> TypeId {
        let key = self.ty_table.lock().unwrap().new_key(TDK::Generic(generic).into());
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
    pub fn canonicalized(
        &self,
    ) -> (
        impl Iterator<Item = (TypeId, TypeData)> + '_,
        &AdtPrototypes,
        &IndexMap<Adt, AdtInstantiation>,
    ) {
        (
            self.ty_keys.iter().map(move |&ty| {
                let td = self.ty_table.lock().unwrap().probe_value(ty);
                (ty, td)
            }),
            &self.adt_prototypes,
            &self.adt_instantiations,
        )
    }
    pub fn create_adt_prototype(&mut self, kind: AdtKind, prototype: AdtPrototype) {
        debug!(?kind, "creating adt prototype");
        match self.adt_prototypes.insert(kind, prototype) {
            None => {}
            _ => todo!("repopulation of adt prototype"),
        }
    }
    pub fn instantiate_adt(
        &mut self,
        db: &dyn crate::Db,
        kind: AdtKind,
        generic_args: GenericArgs,
    ) -> Adt {
        debug!(?kind, "instantiating adt");

        let adt = Adt::new(kind, generic_args);
        if self.adt_instantiations.contains_key(&adt) {
            return adt;
        }

        let ty = self.ty_id(TDK::Adt(adt).into());
        self.adt_tys.insert(adt, ty);

        match self.adt_prototypes.get(kind) {
            None => {
                info!("ADT {} was delayed!", adt.name(db));
            }
            Some(AdtPrototype::StructPrototype(sp)) => self.finish_instantiation(db, adt, sp, ty),
        }
        adt
    }
    pub fn try_adt_ty(&self, adt: Adt) -> Option<TypeId> {
        Some(self.adt_instantiations.get(&adt)?.ty)
    }
    pub fn adt_ty(&mut self, db: &dyn crate::Db, adt: Adt) -> TypeId {
        if let Some(ty) = self.adt_instantiations.get(&adt) {
            return ty.ty;
        }

        let ty = self.adt_tys[&adt];
        // NOTE: Attempt to finish the instantiation
        match self.adt_prototypes.get(adt.kind()) {
            None => info!("ADT {} still delayed...", adt.name(db)),
            Some(AdtPrototype::StructPrototype(sp)) => self.finish_instantiation(db, adt, sp, ty),
        }
        ty
    }

    fn finish_instantiation(
        &mut self,
        db: &dyn crate::Db,
        adt: Adt,
        sp: StructPrototype,
        ty: TypeId,
    ) {
        let fields = sp
            .fields
            .into_iter()
            .map(|(sf, f)| {
                let ty = self.substitude(db, f, &mut |_tc, ty| {
                    sp.generics
                        .iter()
                        .zip(adt.generic_args(db))
                        .find_map(|(param, arg)| if *param == ty { Some(arg) } else { None })
                        .unwrap_or(ty)
                });
                AdtField::new_struct_field(adt, ty, sf)
            })
            .collect();
        self.adt_instantiations.insert(adt, AdtInstantiation { adt, ty, fields });
    }
    pub fn adt_fields(&self, adt: Adt) -> &[AdtField] {
        &self.adt_instantiations[&adt].fields
    }

    pub fn unify(
        &mut self,
        db: &dyn crate::Db,
        expected: TypeId,
        actual: TypeId,
    ) -> Option<TypeId> {
        if self.probe_type(expected).is_void() && self.probe_type(actual).is_void() {
            return Some(expected);
        }

        {
            let mut table = self.ty_table.lock().unwrap();
            if table.unioned(expected, actual) {
                return Some(expected);
            }
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
            (TDK::Builtin(t1, args1), TDK::Builtin(t2, args2))
                if t1 == t2 && args1.len(db) == args2.len(db) =>
            {
                for (l, r) in args1.iter(db).zip_eq(args2.iter(db)) {
                    self.unify(db, l, r)?;
                }
                expected
            }
            (
                TDK::Ref { is_mut: mut1, inner: inner1 },
                TDK::Ref { is_mut: mut2, inner: inner2 },
            ) => {
                let inner = self.unify(db, inner1, inner2)?;
                self.ty_id(TDK::Ref { is_mut: mut1 && mut2, inner }.into())
            }
            (TDK::Optional(inner1), TDK::Optional(inner2)) => {
                self.unify(db, inner1, inner2)?;
                expected
            }
            (TDK::Optional(inner), TDK::Adt(_)) if inner == actual => expected,
            (TDK::Adt(_), TDK::Optional(inner)) if inner == expected => actual,
            (TDK::Primitive(p1), TDK::Primitive(p2)) if p1 == p2 => expected,
            (TDK::Adt(s1), TDK::Adt(s2))
                if s1.kind() == s2.kind() && s1.generic_args_len(db) == s2.generic_args_len(db) =>
            {
                for (l, r) in s1.generic_args(db).zip_eq(s2.generic_args(db)) {
                    self.unify(db, l, r)?;
                }
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

    fn substitude(
        &mut self,
        db: &dyn crate::Db,
        original: TypeId,
        subs: &mut impl FnMut(&mut Self, TypeId) -> TypeId,
    ) -> TypeId {
        let new = subs(self, original);

        if new == original {
            let new_td = self.probe_type(original).map_ty(db, |id| self.substitude(db, id, subs));
            self.ty_id(new_td)
        } else {
            new
        }
    }
}
