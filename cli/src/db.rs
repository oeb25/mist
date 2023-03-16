use mist_core::salsa;

#[derive(Default)]
#[salsa::db(crate::Jar, mist_core::Jar, mist_viper_backend::Jar)]
pub(crate) struct Database {
    storage: salsa::Storage<Self>,
}

impl salsa::Database for Database {}
