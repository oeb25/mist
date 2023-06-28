mod stress;

use std::fmt;

pub(crate) use mist_core::testing::expect;
use mist_core::testing::Fixture;

pub(crate) fn fixture(src: impl fmt::Display) -> (crate::db::Database, Fixture) {
    let db = crate::db::Database::default();
    let fixture = Fixture::new(&db, src);
    (db, fixture)
}
