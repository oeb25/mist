use mist_core::salsa;

#[derive(Default)]
#[salsa::db(mist_core::Jar)]
pub(crate) struct Database {
    storage: salsa::Storage<Self>,
}

impl salsa::Database for Database {}
