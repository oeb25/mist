#![feature(control_flow_enum, get_many_mut)]

mod db;
pub mod def;
pub mod hir;
pub mod mir;
pub mod types;
pub mod util;
pub mod visit;

pub use hir::typecheck::{
    TypeCheckError, TypeCheckErrors, VariableDeclaration, VariableDeclarationKind,
};
pub use salsa;

#[salsa::jar(db = Db)]
pub struct Jar(
    crate::def::Def,
    crate::def::Function,
    crate::def::Struct,
    crate::def::StructField,
    crate::def::TypeInvariant,
    crate::hir::file::parse_file,
    crate::hir::file::ast_map,
    crate::hir::file_context::initialize_file_context,
    crate::hir::SourceFile,
    crate::hir::file_definitions,
    crate::hir::DefinitionHir,
    crate::hir::lower_def,
    crate::hir::typecheck::TypeCheckErrors,
    crate::mir::MirErrors,
    crate::mir::DefinitionMir,
    crate::mir::lower_item,
);

pub trait Db: salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + salsa::DbWithJar<Jar> {}
