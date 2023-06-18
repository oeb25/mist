use mist_syntax::ast::AttrFlags;

use crate::{
    def::Name,
    types::{AdtKind, Primitive},
};

#[salsa::interned]
pub struct Type {
    pub is_ghost: bool,
    pub kind: TypeData,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeData {
    Error,
    Void,
    Ref { is_mut: bool, inner: Type },
    List(Type),
    Optional(Type),
    Primitive(Primitive),
    Adt(Adt),
    Null,
    Function(FunctionType),
    Range(Type),
}

#[salsa::interned]
pub struct FunctionType {
    pub attrs: AttrFlags,
    #[return_ref]
    pub params: Vec<Type>,
    pub return_ty: Type,
}

#[salsa::interned]
pub struct Adt {
    pub kind: AdtKind,
    #[return_ref]
    pub fields: Vec<AdtField>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AdtField {
    pub name: Name,
    pub ty: Type,
}
