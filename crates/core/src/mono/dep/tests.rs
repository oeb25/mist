use std::fmt;

use itertools::Itertools;

use crate::{mono::monomorphized_items, testing::expect, tests::fixture, util::dot::graph_easy};

/// Check that the dependency graph matches in two cases:
/// - An ASCII represenation of the graph is given to `f`. **Note:**
///   [`graph_easy`] requires `Graph::Easy` to be installed. If it is not,
///   this check is skipped.
/// - As a fallback `g` is given a list of edges in the graph.
fn check_dep(src: impl fmt::Display, f: impl FnOnce(String), g: impl FnOnce(String)) {
    let (db, fix) = fixture(src);
    let dep = monomorphized_items(&db, fix.file()).dep(&db);
    let dot = dep.dot(&db);
    if let Ok(fig) = graph_easy(&dot) {
        f(fig);
    }
    let s = dep
        .graph
        .edge_indices()
        .filter_map(|e| {
            let (a, b) = dep.graph.edge_endpoints(e)?;
            let a = dep.graph.node_weight(a)?.name(&db);
            let b = dep.graph.node_weight(b)?.name(&db);
            let l = dep.graph.edge_weight(e)?;
            Some(format!("{a:<15} -> {b:<15} [{l}]"))
        })
        .sorted()
        .dedup()
        .join("\n");
    g(s);
}

fn check_clusters(src: impl fmt::Display, f: impl FnOnce(String)) {
    let (db, fix) = fixture(src);
    let dep = monomorphized_items(&db, fix.file()).dep(&db);
    let s = dep
        .clusters()
        .into_iter()
        .map(|c| {
            let items = c.items.iter().map(|i| i.name(&db)).sorted().format(", ");
            let soft = c.soft.iter().map(|i| i.name(&db)).sorted().format(", ");
            format!("[{{{}}},\n {{{}}}]", items, soft)
        })
        .sorted()
        .join("\n");
    f(s);
}

#[test]
fn dep_basic() {
    check_dep(
        r#"
struct T { f: int }
struct S { t: T }
ghost fn main(x: S);
"#,
        expect!(@r###"
            ┌──────┐
            │ main │
            └──────┘
              │
              │ sig
              ▼
            ┌──────┐
            │  S   │
            └──────┘
              │
              │ sig
              ▼
            ┌──────┐
            │  T   │
            └──────┘
            "###),
        expect!(@r###"
        S               -> T               [sig]
        main            -> S               [sig]
        "###),
    );
}

#[test]
fn dep_body() {
    check_dep(
        r#"
struct T { f: int }
struct S { t: T }
fn f(x: S) {
    g();
}
fn g() { h() }
ghost fn h() req { T {} };
"#,
        expect!(@r###"
            ┌───┐  sig   ┌──────┐
            │ S │ ◀───── │  f   │
            └───┘        └──────┘
              │            │
              │            │ bod
              │            ▼
              │          ┌──────┐
              │          │  g   │
              │          └──────┘
              │            │
              │            │ bod
              │            ▼
              │          ┌──────┐
              │          │  h   │
              │          └──────┘
              │            │
              │            │ sig
              │            ▼
              │   sig    ┌──────┐
              └────────▶ │  T   │
                         └──────┘
            "###),
        expect!(@r###"
        S               -> T               [sig]
        f               -> S               [sig]
        f               -> g               [bod]
        g               -> h               [bod]
        h               -> T               [sig]
        "###),
    );
    check_dep(
        r#"
fn f() { g() }
fn g() { h() }
pure fn h() { i() }
pure fn i() { }
"#,
        expect!(@r###"
            ┌──────┐
            │  f   │
            └──────┘
              │
              │ bod
              ▼
            ┌──────┐
            │  g   │
            └──────┘
              │
              │ bod
              ▼
            ┌──────┐
            │  h   │
            └──────┘
              │
              │ sig
              ▼
            ┌──────┐
            │  i   │
            └──────┘
            "###),
        expect!(@r###"
        f               -> g               [bod]
        g               -> h               [bod]
        h               -> i               [sig]
        "###),
    );
}

#[test]
fn dep_generic() {
    check_dep(
        r#"
struct T[L, R] {}
struct S {}
ghost fn f(x: T[int, S]);
ghost fn g(x: T[int, int]);
"#,
        expect!(@r###"
            ┌─────────────┐
            │      g      │
            └─────────────┘
              │
              │ sig
              ▼
            ┌─────────────┐
            │ T[int, int] │
            └─────────────┘
            ┌─────────────┐
            │      f      │
            └─────────────┘
              │
              │ sig
              ▼
            ┌─────────────┐
            │  T[int, S]  │
            └─────────────┘
              │
              │ sig
              ▼
            ┌─────────────┐
            │      S      │
            └─────────────┘
            "###),
        expect!(@r###"
        T[int, S]       -> S               [sig]
        f               -> T[int, S]       [sig]
        g               -> T[int, int]     [sig]
        "###),
    );

    check_dep(
        r#"
struct A[T] { q: T }
struct B[S, T] { x: A[S], y: A[T] }
ghost fn f(x: B[A[int], B[bool, int]]);
"#,
        expect!(@r###"
                   ┌─────────────────┐
                   │        f        │
                   └─────────────────┘
                     │
                     │ sig
                     ▼
                   ┌─────────────────────────┐  sig   ┌───────────┐
             ┌──── │ B[A[int], B[bool, int]] │ ─────▶ │ A[A[int]] │
             │     └─────────────────────────┘        └───────────┘
             │       │                  │               │
             │       │ sig              │               │
             │       ▼                  │               │
             │     ┌─────────────────┐  │               │
             │     │ A[B[bool, int]] │  │               │
             │     └─────────────────┘  │               │
             │       │                  │ sig           │
             │       │ sig              │               │
             │       ▼                  │               │
             │     ┌─────────────────┐  │               │
        ┌────┼──── │  B[bool, int]   │ ◀┘               │
        │    │     └─────────────────┘                  │
        │    │       │                                  │
        │    │ sig   │ sig                              │
        │    │       ▼                                  │
        │    │     ┌─────────────────┐         sig      │
        │    └───▶ │     A[int]      │ ◀────────────────┘
        │          └─────────────────┘
        │   sig    ┌─────────────────┐
        └────────▶ │     A[bool]     │
                   └─────────────────┘
                   ┌─────────────────┐
                   │      A[S]       │
                   └─────────────────┘
                   ┌─────────────────┐
                   │      A[T]       │
                   └─────────────────┘
        "###),
        expect!(@r###"
        A[A[int]]       -> A[int]          [sig]
        A[B[bool, int]] -> B[bool, int]    [sig]
        B[A[int], B[bool, int]] -> A[A[int]]       [sig]
        B[A[int], B[bool, int]] -> A[B[bool, int]] [sig]
        B[A[int], B[bool, int]] -> A[int]          [sig]
        B[A[int], B[bool, int]] -> B[bool, int]    [sig]
        B[bool, int]    -> A[bool]         [sig]
        B[bool, int]    -> A[int]          [sig]
        f               -> B[A[int], B[bool, int]] [sig]
        "###),
    );
}

#[test]
fn dep_clusters() {
    check_clusters(
        r#"
fn f(x: X)
struct X { y: Y }
struct Y { }
"#,
        expect!(@r###"
            [{X, Y, f},
             {}]
            "###),
    );
    check_clusters(
        r#"
fn f() { g() }
fn g() { h() }
fn h() { }
"#,
        expect!(@r###"
            [{f},
             {g}]
            [{g},
             {h}]
            [{h},
             {}]
            "###),
    );
    check_clusters(
        r#"
fn f() { g() }
fn g() { h() }
pure fn h() { i() }
pure fn i() { }
"#,
        expect!(@r###"
            [{f},
             {g}]
            [{g},
             {h, i}]
            [{h, i},
             {}]
            "###),
    );
    check_clusters(
        r#"
fn f() { g() }
fn g() { h(); h(); q() }
fn h() { f() }
fn q() { }
"#,
        expect!(@r###"
            [{f},
             {g}]
            [{g},
             {h, q}]
            [{h},
             {f}]
            [{q},
             {}]
            "###),
    );
    check_clusters(
        r#"
pure fn f() { g() }
pure fn g() { h(); q() }
pure fn h() { f() }
pure fn q() { }
"#,
        expect!(@r###"
            [{f, g, h, q},
             {}]
            "###),
    );
}
