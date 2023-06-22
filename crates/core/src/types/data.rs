use std::collections::HashMap;

use crate::{
    def::{Name, Struct, StructField},
    hir::{Param, TypeSrc},
    util::impl_idx,
};
use derive_more::From;
use mist_syntax::ast::AttrFlags;
use tracing::error;

use super::{builtin::BuiltinField, primitive::error, BuiltinKind, TypeId};

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
    Optional(T),
    Primitive(Primitive),
    Adt(Adt),
    Builtin(BuiltinKind, GenericArgs),
    Null,
    Function {
        attrs: AttrFlags,
        name: Option<Name>,
        params: Vec<Param<Name, TypeSrc>>,
        return_ty: T,
    },
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
    Enum,
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
    Delayed,
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
    Builtin(BuiltinField<TypeId>),
    Undefined,
}

impl Field {
    pub fn name(&self, db: &dyn crate::Db) -> Name {
        match self {
            Field::AdtField(af) => af.name(db),
            Field::Builtin(bf) => bf.name(),
            Field::Undefined => Name::new("?undefined"),
        }
    }
    pub fn is_ghost(&self, db: &dyn crate::Db) -> bool {
        match self {
            Field::AdtField(af) => af.is_ghost(db),
            Field::Builtin(bf) => bf.is_ghost(),
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
    pub(super) fn new(kind: AdtKind, generic_args: GenericArgs) -> Self {
        Adt { kind, generic_args }
    }
    pub fn struct_(&self) -> Option<Struct> {
        match self.kind {
            AdtKind::Struct(s) => Some(s),
            AdtKind::Enum => todo!(),
        }
    }
    pub fn kind(&self) -> AdtKind {
        self.kind
    }
    pub fn generic_args_len(&self, db: &dyn crate::Db) -> usize {
        self.generic_args.args(db).len()
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
            AdtKind::Enum => todo!(),
        }
    }
    pub fn arity(&self, db: &dyn crate::Db) -> usize {
        match self {
            AdtKind::Struct(s) => {
                s.ast_node(db).generic_param_list().map_or(0, |g| g.generic_params().count())
            }
            AdtKind::Enum => todo!(),
        }
    }
}

impl GenericArgs {
    pub fn none(db: &dyn crate::Db) -> GenericArgs {
        GenericArgs::new(db, Vec::new())
    }
    pub fn len(self, db: &dyn crate::Db) -> usize {
        self.args(db).len()
    }
    pub fn get(self, db: &dyn crate::Db, index: usize) -> TypeId {
        self.args(db).get(index).copied().unwrap_or_else(error)
    }
    pub fn iter(self, db: &dyn crate::Db) -> impl Iterator<Item = TypeId> + '_ {
        self.args(db).iter().copied()
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
            TDK::Optional(it) => TDK::Optional(f(it)),
            TDK::Primitive(it) => TDK::Primitive(*it),
            TDK::Adt(it) => TDK::Adt(*it),
            TDK::Builtin(it, args) => TDK::Builtin(*it, *args),
            TDK::Null => TDK::Null,
            TDK::Function { attrs, name, params, return_ty } => TDK::Function {
                attrs: *attrs,
                name: name.clone(),
                params: params.clone(),
                return_ty: f(return_ty),
            },
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
impl TypeData<TypeId> {
    pub fn map_ty(
        &self,
        db: &dyn crate::Db,
        mut f: impl FnMut(TypeId) -> TypeId,
    ) -> TypeData<TypeId> {
        let kind = match &self.kind {
            TDK::Error => TDK::Error,
            TDK::Void => TDK::Void,
            TDK::Ref { is_mut, inner } => TDK::Ref { is_mut: *is_mut, inner: f(*inner) },
            TDK::Optional(it) => TDK::Optional(f(*it)),
            TDK::Primitive(it) => TDK::Primitive(*it),
            TDK::Adt(it) => TDK::Adt(Adt::new(
                it.kind(),
                GenericArgs::new(db, it.generic_args(db).map(f).collect()),
            )),
            TDK::Builtin(it, args) => {
                TDK::Builtin(*it, GenericArgs::new(db, args.iter(db).map(f).collect()))
            }
            TDK::Null => TDK::Null,
            TDK::Function { attrs, name, params, return_ty } => TDK::Function {
                attrs: *attrs,
                name: name.clone(),
                params: params.clone(),
                return_ty: f(*return_ty),
            },
            TDK::Generic(g) => TDK::Generic(*g),
            TDK::Free => TDK::Free,
        };
        TypeData { is_ghost: self.is_ghost, kind }
    }

    pub(crate) fn builtin(db: &dyn crate::Db, kind: BuiltinKind, tys: &[TypeId]) -> TypeData {
        TDK::Builtin(kind, GenericArgs::new(db, tys.to_vec())).into()
    }
    pub(crate) fn list(db: &dyn crate::Db, ty: TypeId) -> TypeData {
        Self::builtin(db, BuiltinKind::List, &[ty])
    }
    pub(crate) fn range(db: &dyn crate::Db, ty: TypeId) -> TypeData {
        Self::builtin(db, BuiltinKind::Range, &[ty])
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
