use itertools::Itertools;
use mist_core::{
    mono::types::{Adt, AdtField},
    types::AdtKind,
};

pub fn mangled_adt(db: &dyn crate::Db, adt: Adt) -> String {
    match adt.kind(db) {
        AdtKind::Struct(s) => {
            format!(
                "${}{}",
                s.name(db),
                adt.generic_args(db)
                    .iter()
                    .map(|ty| format!("$_{}", ty.display(db).to_string()))
                    .format("")
            )
        }
        AdtKind::Enum => todo!(),
    }
}
pub fn mangled_adt_field(db: &dyn crate::Db, adt: Adt, f: AdtField) -> String {
    format!("{}_$_{}", mangled_adt(db, adt), f.name(db))
}
