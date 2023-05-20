#![feature(trait_upcasting)]

pub mod gen;
pub mod lower;

#[salsa::jar(db=Db)]
pub struct Jar(
    crate::gen::viper_file,
    crate::gen::ViperHints,
    crate::lower::ViperLowerErrors,
);

pub trait Db: mist_core::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + mist_core::Db + salsa::DbWithJar<Jar> {}
