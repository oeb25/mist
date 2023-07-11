use mist_core::mono::types::{Adt, AdtField};

pub fn mangled_adt(db: &dyn crate::Db, adt: Adt) -> String {
    format!("${}", adt.display(db))
        .replace('[', "$lbra_")
        .replace(']', "$rbra_")
        .replace(", ", "_$_")
}
pub fn mangled_adt_field(db: &dyn crate::Db, adt: Adt, f: AdtField) -> String {
    format!("{}_$_{}", mangled_adt(db, adt), f.name(db))
}
