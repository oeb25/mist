use mist_core::def;

pub fn mangled_struct(db: &dyn crate::Db, s: def::Struct) -> String {
    format!("${}", s.name(db))
}
pub fn mangled_field(db: &dyn crate::Db, f: def::StructField) -> String {
    format!(
        "{}_$_{}",
        mangled_struct(db, f.parent_struct(db)),
        f.name(db)
    )
}
