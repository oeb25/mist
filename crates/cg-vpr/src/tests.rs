mod generation;

use std::{
    fmt,
    sync::{Arc, Mutex},
};

use mist_core::{
    salsa::{self, DebugWithDb},
    testing::Fixture,
};

#[derive(Default)]
#[salsa::db(crate::Jar, mist_core::Jar)]
pub(crate) struct Database {
    storage: salsa::Storage<Self>,
    logs: Option<Arc<Mutex<Vec<String>>>>,
}

impl salsa::Database for Database {
    fn salsa_event(&self, event: salsa::Event) {
        if let Some(logs) = &self.logs {
            if let salsa::EventKind::WillExecute { .. } = event.kind {
                logs.lock().unwrap().push(format!("Event: {:?}", event.debug(self)))
            }
        }
    }
}

impl salsa::ParallelDatabase for Database {
    fn snapshot(&self) -> salsa::Snapshot<Self> {
        salsa::Snapshot::new(Database { storage: self.storage.snapshot(), logs: self.logs.clone() })
    }
}

pub(crate) fn fixture(src: impl fmt::Display) -> (Database, Fixture) {
    let db = Database::default();
    let fixture = Fixture::new(&db, src);
    (db, fixture)
}
