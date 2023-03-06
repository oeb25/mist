#![feature(trait_upcasting)]

pub mod db;
pub mod gen;

use miette::{miette, IntoDiagnostic, Result};
use mist_syntax::ast::{Item, SourceFile, Struct};
use silvers::{
    program::{LocalVarDecl, Predicate, Program},
    typ::{AtomicType, Type},
};
use tracing::info;

#[salsa::jar(db=Db)]
pub struct Jar(crate::gen::viper_file, crate::gen::viper_function);

pub trait Db: mist_core::Db + salsa::DbWithJar<Jar> {}

impl<DB> Db for DB where DB: ?Sized + mist_core::Db + salsa::DbWithJar<Jar> {}
