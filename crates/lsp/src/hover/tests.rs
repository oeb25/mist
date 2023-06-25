use std::fmt;

use itertools::Itertools;

use crate::tests::*;

use super::{hover, HoverElement};

fn check_hover_at(src: impl fmt::Display, f: impl FnOnce(String)) {
    let (db, fix) = fixture(src);
    let m = fix.marker(0);
    f(match hover(&db, fix.file(), m.byte_offset()) {
        Some(hr) => hr
            .contents
            .into_iter()
            .map(|e| match e {
                HoverElement::String(s) => s,
                HoverElement::Code(c) => c.lines().map(|l| format!("> {l}")).join("\n"),
            })
            .join("\n---\n"),
        None => "<nothing>".to_string(),
    })
}

#[test]
fn hover_struct() {
    check_hover_at(
        r#"
struct Test {}
invariant $0Test {}
"#,
        expect!(@"> struct Test"),
    );
    check_hover_at(
        r#"
struct Test { field: int }
invariant Test { self.field$0 == 5 }
"#,
        expect!(@r###"
        > struct Test
        ---
        > field: int
        "###),
    );
}

#[test]
fn hover_generic() {
    check_hover_at(
        r#"
struct Test[T] {}
invariant[T] $0Test[T] {}
"#,
        expect!(@"> struct Test[T]"),
    );
    check_hover_at(
        r#"
struct Test[T] { field: T }
invariant[T] Test[T] { self.field$0 == 5 }
"#,
        expect!(@r###"
        > struct Test[T]
        ---
        > field: T
        "###),
    );
    check_hover_at(
        r#"
struct Test[T] { field: T }
invariant Test[int] { self.field$0 == 5 }
"#,
        expect!(@r###"
        > struct Test[T]
        ---
        > field: int
        "###),
    );
}
