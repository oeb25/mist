use std::fmt;

pub(crate) use mist_core::testing::expect;

use crate::gen::{viper_file, ViperOutput};

use super::fixture;

fn check_gen(src: impl fmt::Display, f: impl FnOnce(String)) {
    let (db, fix) = fixture(src);
    let (viper_program, viper_body, _viper_source_map) = viper_file(&db, fix.file()).unwrap();
    let viper_output = ViperOutput::generate_without_prelude(&viper_body, &viper_program);
    f(viper_output.buf);
}

#[test]
fn method() {
    check_gen(
        r#"
fn f() -> int { 12 }
"#,
        expect!(@r###"
        method f() returns (_0: Int) {
          _0 := 12
          label end
        }
        "###),
    );
}

#[test]
fn function() {
    check_gen(
        r#"
pure fn f() -> int { 12 }
"#,
        expect!(@r###"
        function f(): Int {
          12
        }
        "###),
    );
    check_gen(
        r#"
pure fn f(a: int) -> int { g(a, -a) }
pure fn g(a: int, b: int) -> int { a + b }
"#,
        expect!(@r###"
        function f(_1: Int): Int {
          g(_1, -_1)
        }
        function g(_1: Int, _2: Int): Int {
          (_1 + _2)
        }
        "###),
    );
}
