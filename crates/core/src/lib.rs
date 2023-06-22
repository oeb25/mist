#![feature(control_flow_enum, get_many_mut)]

mod db;
pub mod def;
pub mod file;
pub mod hir;
pub mod mir;
pub mod mono;
pub mod types;
pub mod util;
pub mod visit;

pub use hir::typecheck::{
    TypeCheckError, TypeCheckErrors, VariableDeclaration, VariableDeclarationKind,
};
pub use salsa;

#[salsa::jar(db = Db)]
pub struct Jar(
    // file
    crate::file::SourceFile,
    crate::file::SourceFile_parse,
    crate::file::SourceFile_ast_map,
    // def
    crate::def::Def,
    crate::def::Function,
    crate::def::Struct,
    crate::def::StructField,
    crate::def::Enum,
    crate::def::TypeInvariant,
    crate::def::SourceFile_definitions,
    // types
    crate::types::GenericArgs,
    // hir
    crate::hir::file_context::initialize_file_context,
    crate::hir::def::Variable,
    crate::hir::def::TypeSrc,
    crate::hir::def::TypeRef,
    crate::hir::DefinitionHir,
    crate::hir::lower_def,
    crate::hir::typecheck::TypeCheckErrors,
    // mono
    crate::mono::types::Type,
    crate::mono::types::BuiltinType,
    crate::mono::types::Adt,
    crate::mono::types::AdtField,
    crate::mono::types::FunctionType,
    crate::mono::Function,
    crate::mono::monomorphized_items,
    crate::mono::Monomorphized,
    crate::mono::Item,
    // mir
    crate::mir::MirErrors,
    crate::mir::ItemMir,
    crate::mir::lower_item,
);

pub trait Db: salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + salsa::DbWithJar<Jar> {}
