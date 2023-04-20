#![feature(trait_upcasting)]

use mist_core::salsa;

pub mod backend;
mod db;
mod goto;
mod highlighting;
mod hover;
mod viper;

#[salsa::jar(db=Db)]
pub struct Jar(
    crate::highlighting::highlighting,
    crate::highlighting::semantic_tokens,
    crate::highlighting::inlay_hints,
    crate::hover::hover,
    crate::goto::goto_declaration,
);

pub trait Db: mist_cli::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + mist_cli::Db + salsa::DbWithJar<Jar> {}
