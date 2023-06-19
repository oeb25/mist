use itertools::Itertools;
use mist_core::mono::types::{Adt, AdtField};

pub fn mangled_adt(db: &dyn crate::Db, adt: Adt) -> String {
    format!(
        "${}{}",
        adt.name(db),
        adt.generic_args(db)
            .iter()
            .map(|ty| format!("$_{}", ty.display(db).to_string()))
            .format("")
    )
}
pub fn mangled_adt_field(db: &dyn crate::Db, adt: Adt, f: AdtField) -> String {
    format!("{}_$_{}", mangled_adt(db, adt), f.name(db))
}
