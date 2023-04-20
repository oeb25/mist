use mist_core::salsa;

// TODO: This should perhaps be pub(crate)
#[derive(Default)]
#[salsa::db(crate::Jar, mist_core::Jar, mist_viper_backend::Jar)]
pub struct Database {
    storage: salsa::Storage<Self>,
}

impl salsa::Database for Database {}
