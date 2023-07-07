use std::fmt;

use crate::{mir, mono, testing::expect};

use crate::tests::fixture;

fn check_mir(src: impl fmt::Display, f: impl FnOnce(String)) {
    let (db, fix) = fixture(src);

    let item = mono::monomorphized_items(&db, fix.file()).items(&db)[0];
    let mir = mir::lower_item(&db, item).unwrap();
    let ib = mir.ib(&db);

    let s = ib.serialize(&db, mir::serialize::Color::No);

    f(s)
}

#[test]
fn mir_quantifier() {
    check_mir(
        r#"
fn f() requires forall i in 0..10 { true };
"#,
        expect!(@r###"
        :B0
          !forall %2_i :: :B1
        :B1
          !call %3 := (#range[from-to] $0 $10) -> :B2
        :B2
          !call %4 := (#in_range %2_i %3) -> :B3
        :B3
          !switch %4 { 1 -> :B4, otherwise :B5 }
        :B4
          !goto :B7
        :B5
          %5 := $true
          !goto :B6
        :B6
          :quatifier-end :B8
        :B7
          %5 := $true
          !goto :B6
        :B8
        "###),
    );
}
