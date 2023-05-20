use std::sync::{Arc, Mutex};

use mist_core::salsa::{self, DebugWithDb};

// TODO: This should perhaps be pub(crate), but we use it in main, which does
// not have crate access
#[derive(Default)]
#[salsa::db(crate::Jar, mist_core::Jar, mist_codegen_viper::Jar)]
pub struct Database {
    storage: salsa::Storage<Self>,
    logs: Option<Arc<Mutex<Vec<String>>>>,
}

impl salsa::Database for Database {
    fn salsa_event(&self, event: salsa::Event) {
        if let Some(logs) = &self.logs {
            if let salsa::EventKind::WillExecute { .. } = event.kind {
                logs.lock()
                    .unwrap()
                    .push(format!("Event: {:?}", event.debug(self)))
            }
        }
    }
}

impl salsa::ParallelDatabase for Database {
    fn snapshot(&self) -> salsa::Snapshot<Self> {
        salsa::Snapshot::new(Database {
            storage: self.storage.snapshot(),
            logs: self.logs.clone(),
        })
    }
}
