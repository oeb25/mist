#[derive(Default)]
#[salsa::db(crate::Jar, mist_core::Jar)]
pub struct Database {
    storage: salsa::Storage<Self>,
}

impl salsa::Database for Database {}
