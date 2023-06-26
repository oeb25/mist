use std::fmt;

use itertools::Itertools;
use mist_core::mir;
pub(crate) use mist_core::testing::expect;
use mist_syntax::{ast::Spanned, SourceSpan};

use crate::gen::{viper_file, ViperOutput};

use super::fixture;

fn check_trace(src: impl fmt::Display, f: impl FnOnce(String)) {
    let (db, fix) = fixture(src);
    let (viper_program, viper_body, viper_source_map) = viper_file(&db, fix.file()).unwrap();
    let viper_output = ViperOutput::generate_without_prelude(&viper_body, &viper_program);

    let m = fix.span(0);

    let hit = viper_output
        .buf
        .char_indices()
        .filter_map(|(bo, _)| {
            let back = viper_output.trace_expr(SourceSpan::new_start_end(bo, bo))?;
            let (item, back) = viper_source_map.trace_exp(back)?;
            let item_mir = mir::lower_item(&db, item)?;
            let expr = item_mir.source_map(&db).trace_expr(back)?;
            if expr.ast(&db).span().contains_span(m) {
                // if m.contains_span(expr.ast(&db).span()) {
                // if expr.ast(&db).span().contains_span(m) {
                Some(bo)
            } else {
                None
            }
        })
        .collect_vec();

    let s: String = viper_output
        .buf
        .char_indices()
        .map(|(idx, c)| {
            if c == '\n' {
                c
            } else if hit.contains(&idx) {
                '^'
            } else {
                ' '
            }
        })
        .collect();

    let s = viper_output
        .buf
        .lines()
        .interleave(s.lines())
        .enumerate()
        .filter_map(|(i, l)| {
            let l = l.trim_end();
            if i % 2 == 0 {
                Some(l)
            } else if l.is_empty() {
                None
            } else {
                Some(l)
            }
        })
        .join("\n");

    f(s);
}

#[test]
fn trace_req() {
    check_trace(
        r#"
ghost fn f() req $0true$0;
"#,
        expect!(@r###"
        method f()
          requires
            true
            ^^^^
        "###),
    );
    check_trace(
        r#"
ghost fn f(x: int) req forall(y) { $0x == y$0 };
"#,
        expect!(@r###"
        method f(_1: Int)
          requires
            (forall _3: Int :: (_1 == _3))
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        "###),
    );
    check_trace(
        r#"
ghost fn f(x: int) req true, $0false$0, false;
"#,
        expect!(@r###"
        method f(_1: Int)
          requires
            true
          requires
            false
            ^^^^^
          requires
            false
        "###),
    );
    check_trace(
        r#"
ghost fn f(x: int) req true && $0false$0 && false;
"#,
        expect!(@r###"
        method f(_1: Int)
          requires
            (true && (false && false))
            ^^^^^^^^^^^^^^^^^^^^^^^^^^
        "###),
    );
}

#[test]
fn trace_body() {
    check_trace(
        r#"
fn f() {
    let x = $012$0;
}
    "#,
        expect!(@r###"
        method f() {
          var x_1: Int;
          x_1 := 12
                 ^^
          label end
        }
        "###),
    );
    check_trace(
        r#"
fn f() {
    let x = 10 + $012$0 + 14;
}
    "#,
        expect!(@r###"
        method f() {
          var x_1: Int; var _2: Int;
          _2 := (10 + 12)
                ^^^^^^^^^
          x_1 := (_2 + 14)
                 ^^^^^^^^^
          label end
        }
        "###),
    );
}
