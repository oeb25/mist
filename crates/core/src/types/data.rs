use std::fmt;

use crate::{
    def::{Struct, StructField},
    hir::{Name, Param},
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
    Struct(Struct),
    Null,
    Function {
        attrs: AttrFlags,
        name: Option<Name>,
        params: Vec<Param<Name>>,
        return_ty: T,
    },
    Range(T),
    Free,
}
impl_idx!(TypeDataIdx, TypeData, default_debug);
use TypeDataKind as TDK;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Primitive {
    Int,
    Bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, From)]
pub enum Field {
    StructField(StructField),
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
            Field::StructField(sf) => sf.name(db),
            Field::List(_, lf) => Name::new(&lf.to_string()),
            Field::Undefined => Name::new("?undefined"),
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
            (
                TypeData {
                    kind: TDK::Free, ..
                },
                other,
            )
            | (
                other,
                TypeData {
                    kind: TDK::Free, ..
                },
            ) => Ok(other.clone()),
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
            TDK::Ref { is_mut, inner } => TDK::Ref {
                is_mut: *is_mut,
                inner: f(inner),
            },
            TDK::List(it) => TDK::List(f(it)),
            TDK::Optional(it) => TDK::Optional(f(it)),
            TDK::Primitive(it) => TDK::Primitive(it.clone()),
            TDK::Struct(it) => TDK::Struct(*it),
            TDK::Null => TDK::Null,
            TDK::Function {
                attrs,
                name,
                params,
                return_ty,
            } => TDK::Function {
                attrs: *attrs,
                name: name.clone(),
                params: params.clone(),
                return_ty: f(return_ty),
            },
            TDK::Range(it) => TDK::Range(f(it)),
            TDK::Free => TDK::Free,
        };
        TypeData {
            is_ghost: self.is_ghost,
            kind,
        }
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
        TypeData {
            is_ghost: false,
            kind,
        }
    }
}

impl<T> TDK<T> {
    pub fn ghost(self) -> TypeData<T> {
        TypeData {
            is_ghost: true,
            kind: self,
        }
    }
}
