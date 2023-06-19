use std::{collections::HashMap, fmt};

use crate::{
    def::{Name, Struct, StructField},
    hir::{Param, TypeSrc},
    util::impl_idx,
};
use derive_more::From;
use mist_syntax::ast::AttrFlags;
use tracing::error;

use super::TypeId;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeData<T = TypeId> {
    pub is_ghost: bool,
    pub kind: TypeDataKind<T>,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeDataKind<T> {
    Error,
    Void,
    Ref {
        is_mut: bool,
        inner: T,
    },
    List(T),
    Optional(T),
    Primitive(Primitive),
    Adt(Adt),
    Null,
    Function {
        attrs: AttrFlags,
        name: Option<Name>,
        params: Vec<Param<Name, TypeSrc>>,
        return_ty: T,
    },
    Range(T),
    Generic(Generic),
    Free,
}
impl_idx!(TypeDataIdx, TypeData, default_debug);
use TypeDataKind as TDK;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Adt {
    kind: AdtKind,
    generic_args: GenericArgs,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AdtKind {
    Struct(Struct),
}

#[salsa::interned]
pub struct GenericArgs {
    #[return_ref]
    pub args: Vec<TypeId>,
}
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Generic {
    _filler: (),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdtPrototype {
    StructPrototype(StructPrototype),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructPrototype {
    pub parent: Struct,
    pub generics: Vec<TypeId>,
    pub fields: HashMap<StructField, TypeId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Primitive {
    Int,
    Bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, From)]
pub struct AdtField {
    adt: Adt,
    ty: TypeId,
    kind: AdtFieldKind,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, From)]
pub enum AdtFieldKind {
    StructField(StructField),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, From)]
pub enum Field {
    AdtField(AdtField),
    List(TypeId, ListField),
    Undefined,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, From)]
pub enum ListField {
    Len,
}

impl Field {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        match self {
            Field::AdtField(af) => af.name(db),
            Field::List(_, lf) => Name::new(&lf.to_string()),
            Field::Undefined => Name::new("?undefined"),
        }
    }
    pub fn is_ghost(&self, db: &dyn crate::Db) -> bool {
        match self {
            Field::AdtField(af) => af.is_ghost(db),
            Field::List(_, _) => false,
            Field::Undefined => false,
        }
    }
}

impl AdtField {
    pub fn adt(&self) -> Adt {
        self.adt
    }
    pub fn kind(&self) -> AdtFieldKind {
        self.kind
    }
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        match self.kind {
            AdtFieldKind::StructField(sf) => sf.name(db),
        }
    }
    pub fn is_ghost(&self, db: &dyn crate::Db) -> bool {
        match self.kind {
            AdtFieldKind::StructField(sf) => sf.is_ghost(db),
        }
    }

    pub(crate) fn new_struct_field(adt: Adt, ty: TypeId, f: StructField) -> AdtField {
        Self { adt, ty, kind: AdtFieldKind::StructField(f) }
    }

    pub fn ty(&self) -> TypeId {
        self.ty
    }
}

impl Adt {
    pub(super) fn new(db: &dyn crate::Db, kind: AdtKind, generic_args: Vec<TypeId>) -> Self {
        Adt { kind, generic_args: GenericArgs::new(db, generic_args) }
    }
    pub fn struct_(&self) -> Option<Struct> {
        match self.kind {
            AdtKind::Struct(s) => Some(s),
        }
    }
    pub fn kind(&self) -> AdtKind {
        self.kind
    }
    pub fn generic_args<'db>(&self, db: &'db dyn crate::Db) -> impl Iterator<Item = TypeId> + 'db {
        self.generic_args.args(db).iter().copied()
    }
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        self.kind.name(db)
    }
}
impl AdtKind {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        match self {
            AdtKind::Struct(s) => s.name(db),
        }
    }
}

impl fmt::Display for ListField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ListField::Len => write!(f, "len"),
        }
    }
}

impl ena::unify::UnifyValue for TypeData {
    type Error = ();

    fn unify_values(ty1: &Self, ty2: &Self) -> Result<Self, ()> {
        match (ty1, ty2) {
            (TypeData { kind: TDK::Free, .. }, other)
            | (other, TypeData { kind: TDK::Free, .. }) => Ok(other.clone()),
            _ => {
                error!("could not unify {ty1:?} with {ty2:?}");
                Err(())
            }
        }
    }
}

impl<T> TypeData<T> {
    pub fn map<S>(&self, mut f: impl FnMut(&T) -> S) -> TypeData<S> {
        let kind = match &self.kind {
            TDK::Error => TDK::Error,
            TDK::Void => TDK::Void,
            TDK::Ref { is_mut, inner } => TDK::Ref { is_mut: *is_mut, inner: f(inner) },
            TDK::List(it) => TDK::List(f(it)),
            TDK::Optional(it) => TDK::Optional(f(it)),
            TDK::Primitive(it) => TDK::Primitive(*it),
            TDK::Adt(it) => TDK::Adt(*it),
            TDK::Null => TDK::Null,
            TDK::Function { attrs, name, params, return_ty } => TDK::Function {
                attrs: *attrs,
                name: name.clone(),
                params: params.clone(),
                return_ty: f(return_ty),
            },
            TDK::Range(it) => TDK::Range(f(it)),
            TDK::Generic(g) => TDK::Generic(*g),
            TDK::Free => TDK::Free,
        };
        TypeData { is_ghost: self.is_ghost, kind }
    }

    pub fn is_void(&self) -> bool {
        matches!(self.kind, TDK::Void)
    }
    pub fn is_ghost(&self) -> bool {
        self.is_ghost
    }
    pub fn is_error(&self) -> bool {
        matches!(self.kind, TDK::Error)
    }
}
impl<T> From<TDK<T>> for TypeData<T> {
    fn from(kind: TDK<T>) -> Self {
        TypeData { is_ghost: false, kind }
    }
}

impl<T> TDK<T> {
    pub fn ghost(self) -> TypeData<T> {
        TypeData { is_ghost: true, kind: self }
    }
}
