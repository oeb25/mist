use mist_core::salsa;

pub mod backend;
mod db;

#[salsa::jar(db=Db)]
pub struct Jar();

pub trait Db: mist_core::Db + mist_viper_backend::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + mist_core::Db + mist_viper_backend::Db + salsa::DbWithJar<Jar> {}
