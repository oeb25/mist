use std::fmt;

use crate::tests::*;

use super::goto_declaration;

fn check_goto_at(src: impl fmt::Display) {
    let (db, fix) = fixture(src);
    let m = fix.marker(0);
    let s = fix.span(1);
    dbg!(m, s);
    match goto_declaration(&db, fix.file(), m.byte_offset()) {
        Some(spans) => assert_eq!(s, spans.target_span),
        None => panic!(),
    }
}

#[test]
fn goto_struct() {
    check_goto_at(
        r#"
struct $1S$1 {}
fn f(x: $0S) {}
"#,
    );
}

#[test]
fn goto_field() {
    check_goto_at(
        r#"
struct S { $1a$1: int }
fn f(x: S) { x.a$0 }
"#,
    );
}
