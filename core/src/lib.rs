mod db;
pub mod ir;
#[cfg(test)]
mod tests;
mod typecheck;
pub mod util;

pub use salsa;
pub use typecheck::{TypeCheckError, TypeCheckErrors};

#[salsa::jar(db = Db)]
pub struct Jar(
    crate::ir::SourceProgram,
    crate::ir::Program,
    crate::ir::Function,
    crate::ir::Struct,
    crate::ir::Type,
    crate::ir::TypeDecl,
    crate::ir::VariableId,
    crate::ir::Variable,
    crate::ir::parse_program,
    crate::ir::top_level_type_decls,
    crate::ir::struct_name,
    crate::ir::struct_fields,
    crate::ir::functions,
    crate::ir::function_body,
    crate::ir::structs,
    crate::ir::find_type,
    crate::ir::find_named_type,
    crate::typecheck::TypeCheckErrors,
);

pub trait Db: salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + salsa::DbWithJar<Jar> {}
