use std::fmt;

use crate::testing::*;

fn fixture(src: impl fmt::Display) -> (crate::db::Database, Fixture) {
    let db = crate::db::Database::default();
    let fixture = Fixture::new(&db, src);
    (db, fixture)
}

fn check_type_at(src: impl fmt::Display, f: impl FnOnce(String)) {
    let (db, fixture) = fixture(src);
    let m = fixture.marker(0);
    f(fixture.type_at(&db, m).display(&db).to_string())
}

fn check_pure_type(src: impl fmt::Display) -> Option<bool> {
    let (db, fixture) = fixture(src);
    let m = fixture.marker(0);
    fixture.type_at(&db, m).is_pure(&db)
}

fn check_pure_adt(src: impl fmt::Display) -> bool {
    let (db, fixture) = fixture(src);
    let m = fixture.marker(0);
    fixture.adt_at(&db, m).is_pure(&db)
}

#[test]
fn test_type_at() {
    check_type_at(
        r#"
pure struct Pos { x: int }
invariant Pos$0 { true }
"#,
        expect!(@r#"Pos"#),
    );
    check_type_at(
        r#"
pure struct Pos { x: int }
invariant Pos { self$0.x == 4 }
"#,
        expect!(@r#"ghost Pos"#),
    );
}

#[test]
fn test_pure() {
    assert_eq!(
        check_pure_type(
            r#"
pure struct Pos { x: int }
invariant Pos$0 { true }
"#,
        ),
        Some(true)
    );
    assert_eq!(
        check_pure_type(
            r#"
pure struct Pos { x: int }
invariant Pos { self$0.x == 4 }
"#,
        ),
        Some(true)
    );
    assert_eq!(
        check_pure_type(
            r#"
pure struct Pos[T] { x: T }
fn f() {
    let a = Pos$0 { x: 1 };
}
"#,
        ),
        Some(true)
    );
    assert!(check_pure_adt(
        r#"
pure struct Pos[T] { x: T }
fn f() {
    let a = Pos$0 { x: 1 };
}
"#,
    ));
    assert!(check_pure_adt(
        r#"
pure struct Tuple[T, S] {
    fst: T,
    snd: S,
}
fn client() {
    let a = Tuple$0 { fst: 4, snd: 4 };
    let c = Tuple { fst: a, snd: a };
    assert sum(c) == 16;
}
"#,
    ));
}
