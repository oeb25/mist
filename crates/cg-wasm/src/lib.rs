#![feature(trait_upcasting)]

pub mod gen;
pub mod wasm;

#[salsa::jar(db=Db)]
pub struct Jar();

pub trait Db: mist_core::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + mist_core::Db + salsa::DbWithJar<Jar> {}
