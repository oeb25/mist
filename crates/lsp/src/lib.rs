#![feature(trait_upcasting)]

pub mod backend;
mod db;
mod goto;
mod highlighting;
mod hover;
#[cfg(test)]
mod tests;
mod viper;

#[salsa::jar(db=Db)]
pub struct Jar(
    crate::highlighting::highlighting,
    crate::highlighting::semantic_tokens,
    crate::highlighting::inlay_hints,
    crate::hover::hover,
    crate::goto::goto_declaration,
    crate::goto::find_references,
    crate::viper::VerificationInput,
    crate::viper::VerificationErrors,
    crate::viper::verify_viper_src,
    crate::viper::viper_unwind_if_cancelled,
);

pub trait Db: mist_cli::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + mist_cli::Db + salsa::DbWithJar<Jar> {}
