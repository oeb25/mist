use std::fmt;

use itertools::Itertools;
pub(crate) use mist_core::testing::expect;

use crate::gen::{viper_file, ViperOutput};

use super::fixture;

fn check_gen(src: impl fmt::Display, f: impl FnOnce(String)) {
    let (db, fix) = fixture(src);
    let (viper_program, viper_body, _viper_source_map) = viper_file(&db, fix.file()).unwrap();
    let viper_output = ViperOutput::generate_without_prelude(&viper_body, &viper_program);
    f(viper_output.buf.lines().map(|l| l.trim_end()).join("\n"));
}
fn check_gen_err(src: impl fmt::Display, f: impl FnOnce(String)) {
    let (db, fix) = fixture(src);
    let mut err = viper_file(&db, fix.file()).unwrap_err();
    err.populate_spans(&db);
    let err = miette::Error::new(err).with_source_code(fix.file().text(&db).clone());

    let mut out = String::new();
    miette::GraphicalReportHandler::new_themed(miette::GraphicalTheme::unicode_nocolor())
        .render_report(&mut out, err.as_ref())
        .unwrap();
    f(out)
}

#[test]
fn generation_method() {
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
fn generation_function() {
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

#[test]
fn generation_missing_ens() {
    check_gen_err(
        r#"
fn compute() ens
{
    while true {}
    0
}
"#,
        expect!(@r###"
          × not yet implemented: tried to lower a block which should be stopped at
           ╭─[5:1]
         5 │     while true {}
         6 │     0
           ·     ─
         7 │ }
           ╰────
        "###),
    )
}

#[test]
fn generation_larger() {
    check_gen(
        r#"
struct FibTable {
  values: [int]
}

invariant FibTable {
  forall i in 0..self.values.len {
    self.values[i] == fib(i)
  }
}

fn compute_up_to(t: &mut FibTable, n: int)
  ens t.values.len >= n
{
  while t.values.len < n
    dec n - t.values.len
  {
    if t.values.len < 2 {
      t.values = [1, 1];
    } else {
      t.values = t.values + [t.values[t.values.len - 1] + t.values[t.values.len - 2]];
    }
  }
}

pure ghost fn fib(n: int) -> int
  req n >= 0
{
  if n < 2 { 1 } else { fib(n - 1) + fib(n - 2) }
}
"#,
        expect!(@r###"
        field $FibTable_$_values: Seq[Int]
        function fib(_1: Int): Int
          requires
            (_1 >= 0)
        {
          ((_1 < 2)
            ? 1
            : (fib((_1 - 1)) + fib((_1 - 2))))
        }
        predicate $FibTable(_0: Ref) {
          (acc(_0.$FibTable_$_values, write) && (forall _2: Int :: (in_range(_2, range_from_to(0, |_0.$FibTable_$_values|))
            ? (_0.$FibTable_$_values[_2] == fib(_2))
            : true)))
        }
        method compute_up_to(_1: Ref, _2: Int)
          requires
            acc($FibTable(_1), write)
          ensures
            acc($FibTable(_1), write)
          ensures
            (unfolding acc($FibTable(_1), wildcard) in (|_1.$FibTable_$_values| >= _2))
        {
          var _3: Bool; var _4: Bool; var _5: Bool; var _6: Bool; var _7: Int; var _8: Bool; var _9: Seq[Int]; var _10: Int; var _11: Int; var _12: Int; var _13: Int; var _14: Int; var _15: Seq[Int]; var _16: Seq[Int]; var _17: Int;
          unfold acc($FibTable(_1), write)
          _4 := (|_1.$FibTable_$_values| < _2)
          fold acc($FibTable(_1), write)
          while (_4)
            invariant
              acc($FibTable(_1), write)
            invariant
              (unfolding acc($FibTable(_1), wildcard) in ((|_1.$FibTable_$_values| < _2) == _4))
          {
            unfold acc($FibTable(_1), write)
            _7 := (_2 - |_1.$FibTable_$_values|)
            _8 := (|_1.$FibTable_$_values| < 2)
            {
              if (_8)
              {
                _9 := Seq(1, 1)
                _1.$FibTable_$_values := _9
              } else {
                _10 := (|_1.$FibTable_$_values| - 1)
                _11 := _1.$FibTable_$_values[_10]
                _12 := (|_1.$FibTable_$_values| - 2)
                _13 := _1.$FibTable_$_values[_12]
                _14 := (_11 + _13)
                _15 := Seq(_14)
                _16 := (_1.$FibTable_$_values ++ _15)
                _1.$FibTable_$_values := _16
              }
            }
            _17 := (_2 - |_1.$FibTable_$_values|)
            assert (_17 < _7)
            assert (0 <= _7)
            fold acc($FibTable(_1), write)
            unfold acc($FibTable(_1), write)
            _4 := (|_1.$FibTable_$_values| < _2)
            fold acc($FibTable(_1), write)
          }
          label end
        }
        "###),
    )
}
