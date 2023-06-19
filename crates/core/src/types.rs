mod data;
mod provider;
mod ptr;
mod table;
mod unification;

pub use data::{
    Adt, AdtField, AdtFieldKind, AdtKind, AdtPrototype, Field, Generic, GenericArgs, ListField,
    Primitive, StructPrototype, TypeData, TypeDataIdx, TypeDataKind, TypeDataKind as TDK,
};
pub use provider::TypeProvider;
pub use ptr::{TypeDataPtr, TypePtr};
pub use table::TypeTable;
pub use unification::{builtin, TypeId, Typer};
