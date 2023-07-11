#![allow(dead_code)]

//! This module is an attempt at the next iteration of pure code generation,
//! which should reconstruct Viper expressions by tracking data flow, instead of
//! following the procedual instructures directly.
//!
//! The goal is to allows a mixture of procedual and expression-oriented code,
//! and automatically strip out everything not contributing to the final result.

use std::{borrow::Cow, fmt};

use itertools::EitherOrBoth;
use mist_core::{mir, util::IdxMap};

#[salsa::interned]
pub struct PExpr {
    kind: PExprKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PExprKind {
    MExpr(mir::MExpr),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemorySource {
    MExpr(mir::MExpr),
}

#[derive(Debug, Default, Clone)]
struct Memory {
    condition: Vec<(mir::Operand, Option<u128>)>,
    values: IdxMap<mir::LocalId, MemorySource>,
}

fn pure_expr(db: &dyn crate::Db, ib: &mir::ItemBody) -> Option<PExpr> {
    let cfg = mist_core::mir::analysis::cfg::Cfg::compute(db, ib);

    let mut memories = IdxMap::<mir::BlockId, Memory>::new();

    if let Some(bb) = ib.body_block() {
        cfg.visit_reverse_post_order(bb, |bid| {
            let mut entry_mem = ib
                .preceding_blocks(db, bid)
                .map(|i| Cow::Borrowed(&memories[i]))
                .reduce(|a, b| {
                    let new = Memory::default();
                    for (_k, it) in a.values.zip(&b.values) {
                        match it {
                            EitherOrBoth::Both(_, _) => todo!(),
                            EitherOrBoth::Left(_) => todo!(),
                            EitherOrBoth::Right(_) => todo!(),
                        }
                    }
                    Cow::Owned(new)
                })
                .unwrap_or_default()
                .into_owned();

            for inst in bid.instructions(ib) {
                match inst.data(ib) {
                    mir::Instruction::Assign(place, exp) => {
                        if place.has_projection(db) {
                            todo!()
                        }

                        if entry_mem
                            .values
                            .insert(place.local(), MemorySource::MExpr(*exp))
                            .is_some()
                        {
                            todo!()
                        }
                    }
                    mir::Instruction::NewAdt(_, _, _) => todo!(),
                    mir::Instruction::Folding(_) => todo!(),
                    mir::Instruction::PlaceMention(_) => todo!(),
                }
            }

            memories.insert(bid, entry_mem);
        });
    }

    let final_bid = ib.exit_blocks(db).next()?;
    Some(reconstruct(db, &memories[final_bid], ib.result_local()?))
}

fn reconstruct(_db: &dyn crate::Db, mem: &Memory, _local: mir::LocalId) -> PExpr {
    dbg!(mem);

    todo!()

    // match mem.values[local] {
    //     MemorySource::MExpr(exp) => {
    //         match exp {
    //             mir::MExpr::Use(op) => {
    //                 match op {
    //                     mir::Operand::Copy(p)|
    //                     mir::Operand::Move(_) => {
    //                     },
    //                     mir::Operand::Literal(_) => todo!(),
    //                 }
    //             },
    //             mir::MExpr::Ref(_, _) => todo!(),
    //             mir::MExpr::BinaryOp(_, _, _) => todo!(),
    //             mir::MExpr::UnaryOp(_, _) => todo!(),
    //         }
    //     },
    // }
}

impl PExpr {
    pub fn display(self, db: &dyn crate::Db, body: &mir::Body) -> impl fmt::Display {
        match self.kind(db) {
            PExprKind::MExpr(exp) => exp.serialize(mir::serialize::Color::No, db, body),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fmt;

    use mist_core::{mir, mono, testing::expect};

    use crate::tests::fixture;

    use super::pure_expr;

    fn check_pure(src: impl fmt::Display, f: impl FnOnce(String)) {
        let (db, fix) = fixture(src);

        let item = mono::monomorphized_items(&db, fix.file()).items(&db)[0];
        let mir = mir::lower_item(&db, item).unwrap();
        let ib = mir.ib(&db);

        let exp = pure_expr(&db, ib);

        f(exp.expect("could not lower").display(&db, ib).to_string())
    }

    #[test]
    #[ignore = "not yet implemented"]
    fn pure_lower() {
        check_pure(
            r#"
fn f() { 12 }
"#,
            expect!(@"$12"),
        );
        check_pure(
            r#"
fn f() { let x = 12; x }
"#,
            expect!(@"$12"),
        );
    }

    #[test]
    #[ignore = "not yet implemented"]
    fn pure_lower_nested_quantifier() {
        check_pure(
            r#"
pure ghost fn f(n: int) -> bool {
    forall i in 0..n { true }
}
"#,
            expect!(@"$12"),
        );
    }
}
