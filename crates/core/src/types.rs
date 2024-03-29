mod builtin;
mod data;
mod provider;
mod table;
mod unification;

pub use builtin::{BuiltinField, BuiltinKind, ListField, MultiSetField, RangeField, SetField};
pub use data::{
    Adt, AdtField, AdtFieldKind, AdtKind, AdtPrototype, Field, GenericArgs, Primitive,
    StructPrototype, TypeData, TypeDataIdx, TypeDataKind, TypeDataKind as TDK,
};
pub use provider::TypeProvider;
pub use table::TypeTable;
pub use unification::{primitive, TypeId, Typer};
