#![feature(trait_upcasting)]

pub mod gen;
pub mod lower;
pub mod mangle;
#[cfg(test)]
mod tests;

pub use silvers;

#[salsa::jar(db=Db)]
pub struct Jar(
    crate::gen::viper_file,
    crate::gen::viper_item,
    crate::gen::ViperHints,
    crate::lower::ViperLowerErrors,
);

pub trait Db: mist_core::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + mist_core::Db + salsa::DbWithJar<Jar> {}
