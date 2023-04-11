#![feature(control_flow_enum)]

mod db;
pub mod ir;
#[cfg(test)]
mod tests;
mod typecheck;
pub mod util;
pub mod visit;

pub use salsa;
pub use typecheck::{
    TypeCheckError, TypeCheckErrors, VariableDeclaration, VariableDeclarationKind,
};

#[salsa::jar(db = Db)]
pub struct Jar(
    crate::ir::SourceProgram,
    crate::ir::Program,
    crate::ir::Function,
    crate::ir::Struct,
    crate::ir::TypeInvariant,
    crate::ir::Type,
    crate::ir::TypeDecl,
    crate::ir::VariableId,
    crate::ir::Variable,
    crate::ir::parse_program,
    // crate::ir::items,
    crate::ir::item,
    // crate::ir::top_level_type_decls,
    crate::ir::struct_fields,
    crate::ir::struct_ty,
    // crate::ir::functions,
    crate::ir::function_body,
    crate::ir::ty_inv_block,
    // crate::ir::structs,
    crate::ir::find_type,
    crate::ir::find_named_type,
    crate::typecheck::TypeCheckErrors,
);

pub trait Db: salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + salsa::DbWithJar<Jar> {}
