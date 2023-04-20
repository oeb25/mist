use mist_core::salsa;

#[derive(Default)]
#[salsa::db(crate::Jar, mist_core::Jar, mist_viper_backend::Jar, mist_cli::Jar)]
pub(crate) struct Database {
    storage: salsa::Storage<Self>,
}

impl salsa::Database for Database {}

// TODO: We want this, but we need to get rid of all !Send/!Sync types first
// impl salsa::ParallelDatabase for Database {}
