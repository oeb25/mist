#![feature(control_flow_enum)]

mod db;
pub mod hir;
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
    crate::hir::SourceProgram,
    crate::hir::Program,
    crate::hir::Function,
    crate::hir::Struct,
    crate::hir::TypeInvariant,
    crate::hir::Type,
    crate::hir::TypeDecl,
    crate::hir::VariableId,
    crate::hir::Variable,
    crate::hir::parse_program,
    // crate::hir::items,
    crate::hir::item,
    // crate::hir::top_level_type_decls,
    crate::hir::struct_fields,
    crate::hir::struct_ty,
    // crate::hir::functions,
    crate::hir::function_body,
    crate::hir::ty_inv_block,
    // crate::hir::structs,
    crate::hir::find_type,
    crate::hir::find_named_type,
    crate::typecheck::TypeCheckErrors,
);

pub trait Db: salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + salsa::DbWithJar<Jar> {}
