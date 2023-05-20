#![feature(control_flow_enum, get_many_mut)]

mod db;
pub mod hir;
pub mod mir;
pub mod util;
pub mod visit;

pub use hir::typecheck::{
    TypeCheckError, TypeCheckErrors, VariableDeclaration, VariableDeclarationKind,
};
pub use salsa;

#[salsa::jar(db = Db)]
pub struct Jar(
    crate::hir::SourceProgram,
    crate::hir::Program,
    crate::hir::ItemId,
    crate::hir::Function,
    crate::hir::Struct,
    crate::hir::TypeInvariant,
    crate::hir::TypeDecl,
    crate::hir::VariableId,
    crate::hir::Variable,
    crate::hir::parse_program,
    crate::hir::item_lower,
    crate::hir::intern_item,
    crate::hir::typecheck::TypeCheckErrors,
    crate::mir::MirErrors,
    crate::mir::lower_program,
);

pub trait Db: salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + salsa::DbWithJar<Jar> {}
