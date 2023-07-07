use std::fmt;

use crate::{testing::expect, tests::fixture};

fn check_desugar(src: impl fmt::Display, f: impl FnOnce(String)) {
    let (db, fix) = fixture(src);
    let m = fix.marker(0);
    f(fix.expr_at(&db, m).display(&db).to_string())
}

#[test]
fn desugar_quantifier() {
    check_desugar(
        r#"
fn f()
  req forall$0 i in 1..10 { true }$0"#,
        expect!(@r###"
      forall(i: int) { if i in (1..10) {
        true
      } else true }
      "###),
    );
    check_desugar(
        r#"
fn f()
  req forall$0 i in 1..10 { forall j in i..10 { true } }$0"#,
        expect!(@r###"
        forall(i: int) { if i in (1..10) {
          forall(j: int) { if j in (i..10) {
            true
          } else true }
        } else true }
        "###),
    );
}

#[test]
fn desugar_for() {
    check_desugar(
        r#"
fn f() {
    for$0 i in 0..10 {}
}
"#,
        expect!(@r###"
        {
          let i: int = (0..10).min;
          while i < (0..10).max
            inv (0..10).min <= i
            inv (0..10).min > (0..10).max || i <= (0..10).max
          {
            {};
            i = i + 1;
          };
        }
        "###),
    )
}
