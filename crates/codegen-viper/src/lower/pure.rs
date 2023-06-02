//! Lowering of the MIR CFG into a pure expression format (PEF).
//!
//! In PEF there are no reassignments, which is the not case for MIR.
//! Especially in conditional assignment, each final node in condition will
//! perform the assignment to the variable.
//!
//! This means that lowering into PEF is not a straight pass over the CFG.
//! Instead we must determine each branching assignment point, compute the
//! values in each branch, construct the conditional assignment, and then
//! continue from where the branches left off.
//!
//! To do so, we make use of two general concepts:
//! - **Dominating frontiers:** For each node in a branching assignment
//!   subgraph, their frontier will be the must recent branching assignment
//!   node. This allows us to know if a node is part of a branching
//!   assignment, and more importantly, if its immediate successor is. If
//!   its successor is not, then we know that this is the assignment point
//!   of the conditional assignment.
//! - **Postdominating nodes:** This forms a relationship between nodes and
//!   their most immediate successor, which all branches converge at. This
//!   allows us to know where to "jump" to after performing a conditional
//!   assignment.
//!
//! The outline of the lowering algorithm is thus:
//! - Start at the entry block of the CFG.
//! - Generate Viper Expressions (VExpr) for each block recursively:
//!     - Start by looking at the terminator of the block:
//!         - **Goto:** Check if the successor is part of the same
//!           conditional assignment as this once. If it is, generate that
//!           block, and set it as the tail. If it is not, set the tail to
//!           empty.
//!         - **Switch:** There will always be an _otherwise_ case, which is
//!           generated like **Goto**. Starting with the newly generated
//!           tail, perform a reverse fold over the cases, where each case
//!           is generated to terminate before reaching the postdominating
//!           node of the current node. For each generation, we generate a
//!           branch on the current case and the tail. In the end we have a
//!           (potentially nested) conditional where the cases are matched
//!           in order, with the _otherwise_ case as a final fallback.
//!
//!           Finally for switches, we must generate the code for the
//!           postdominating node of the current node, and wrap the
//!           conditional around that.
//!     - With the tail (which is potentially empty) found, we do a reverse
//!       fold over the instructions in the block. Doing this, we
//!       potentially perform an assignment, in which case we must introduce
//!       a `let-in` expression, wrapping the tail of the fold.

use mist_core::{hir, mir};
use silvers::expression::{Exp, PermExp, PredicateAccess, PredicateAccessPredicate, QuantifierExp};
use tracing::warn;

use crate::{gen::VExprId, mangle};

use super::{BlockOrInstruction, BodyLower, Result, ViperLowerError};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PureLowerResult {
    /// An expression ([`VExprId`]) which has not yet been assigned to
    /// [`mir::Place`] and stopped before [`Option<mir::BlockId>`].
    UnassignedExpression(VExprId, mir::Place, Option<mir::BlockId>),
    Empty {
        stopped_before: Option<mir::BlockId>,
    },
}
impl PureLowerResult {
    fn wrap_in_assignment(
        self,
        lower: &mut BodyLower<'_>,
        source: impl Into<BlockOrInstruction> + Copy,
        x: mir::Place,
        exp: VExprId,
    ) -> Result<PureLowerResult> {
        match self {
            PureLowerResult::UnassignedExpression(body, target, stopped_before) => {
                if lower.can_inline(x, exp) {
                    let r = lower.place_to_ref(source, x)?;
                    lower.inlined.insert(r, exp);
                    Ok(self)
                } else {
                    let variable = lower.place_for_assignment(x)?;
                    Ok(PureLowerResult::UnassignedExpression(
                        lower.alloc(source, Exp::new_let(variable.into(), exp, body)),
                        target,
                        stopped_before,
                    ))
                }
            }
            PureLowerResult::Empty { stopped_before } => {
                Ok(PureLowerResult::UnassignedExpression(exp, x, stopped_before))
            }
        }
    }

    fn try_map_exp(self, mut f: impl FnMut(VExprId) -> Result<VExprId>) -> Result<PureLowerResult> {
        Ok(match self {
            PureLowerResult::UnassignedExpression(exp, place, stopped_before) => {
                PureLowerResult::UnassignedExpression(f(exp)?, place, stopped_before)
            }
            PureLowerResult::Empty { stopped_before } => PureLowerResult::Empty { stopped_before },
        })
    }
}

impl BodyLower<'_> {
    pub fn pure_lower(&mut self, entry: mir::BlockId) -> Result<VExprId> {
        self.postdominators = self.cfg.postdominators(entry);
        self.pure_final_block(entry)
    }

    pub fn pure_finish(self) {
        let mut inlines = vec![];
        for (original_id, _) in self.viper_body.arena.iter() {
            let mut id = original_id;
            while let Some(next) = self.inlined.get(id) {
                id = *next;
            }
            if original_id != id {
                inlines.push((original_id, id))
            }
        }
        for (from, to) in inlines {
            self.viper_body.arena[from] = self.viper_body.arena[to].clone();
        }
    }
}

// Perform all inlining when dropping the lowerer
impl<'a> Drop for BodyLower<'a> {
    fn drop(&mut self) {
        let mut inlines = vec![];
        for (original_id, _) in self.viper_body.arena.iter() {
            let mut id = original_id;
            while let Some(next) = self.inlined.get(id) {
                id = *next;
            }
            if original_id != id {
                inlines.push((original_id, id))
            }
        }
        for (from, to) in inlines {
            self.viper_body.arena[from] = self.viper_body.arena[to].clone();
        }
    }
}

impl BodyLower<'_> {
    pub(super) fn pure_block(
        &mut self,
        block: mir::BlockId,
        stop_at: Option<mir::BlockId>,
    ) -> Result<PureLowerResult> {
        if Some(block) == stop_at {
            todo!();
        }

        let start = match self.body[block].terminator() {
            Some(t) => match t {
                mir::Terminator::Return => {
                    return Err(ViperLowerError::NotYetImplemented {
                        msg: "return terminator".to_string(),
                        def: self.body.def(),
                        block_or_inst: Some(block.into()),
                        span: None,
                    })
                }
                mir::Terminator::Quantify(q, over, next) => match self.pure_block(*next, None)? {
                    PureLowerResult::UnassignedExpression(exp, place, stopped_before) => {
                        for s in over {
                            self.internally_bound_slots.insert(*s, ());
                        }

                        let variables =
                            over.iter().map(|s| self.slot_to_decl(*s)).collect::<Result<_>>()?;
                        let triggers = vec![];

                        PureLowerResult::UnassignedExpression(
                            self.alloc(
                                block,
                                match q {
                                    hir::Quantifier::Forall => {
                                        QuantifierExp::Forall { variables, triggers, exp }
                                    }
                                    hir::Quantifier::Exists => {
                                        QuantifierExp::Exists { variables, triggers, exp }
                                    }
                                },
                            ),
                            // TODO
                            place,
                            // self.body.result_slot().unwrap().into(),
                            stopped_before,
                        )
                    }
                    PureLowerResult::Empty { .. } => {
                        return Err(ViperLowerError::NotYetImplemented {
                            msg: "quantifier with empty result".into(),
                            def: self.body.def(),
                            block_or_inst: Some(block.into()),
                            span: None,
                        })
                    }
                },
                mir::Terminator::QuantifyEnd(next) => {
                    PureLowerResult::Empty { stopped_before: Some(*next) }
                }
                &mir::Terminator::Goto(next) => {
                    if stop_at == Some(next) {
                        PureLowerResult::Empty { stopped_before: Some(next) }
                    } else {
                        self.pure_block(next, stop_at)?
                    }
                }
                mir::Terminator::Switch(test, switch) => {
                    let Some(next) = self.postdominators.get(block) else {
                        return Err(ViperLowerError::NotYetImplemented {
                            msg: format!("block {block} did not have a postdominator"),
                            def: self.body.def(),
                            block_or_inst: Some(block.into()),
                            span: None,
                        })
                    };

                    let (mut values, otherwise) = switch.values();
                    let otherwise_result = self.pure_block(otherwise, Some(next))?;
                    let cont = values.try_fold(otherwise_result, |els, (value, target)| {
                        match (els, self.pure_block(target, Some(next))?) {
                            (
                                PureLowerResult::UnassignedExpression(els, els_slot, _),
                                PureLowerResult::UnassignedExpression(thn, thn_slot, _),
                            ) => {
                                if thn_slot != els_slot {
                                    return Err(ViperLowerError::NotYetImplemented {
                                        msg: "divergent branches".to_string(),
                                        def: self.body.def(),
                                        block_or_inst: Some(block.into()),
                                        span: None,
                                    });
                                }
                                let cond = match value {
                                    1 => self.operand_to_ref(block, test)?,
                                    _ => todo!(), // Exp::new_bin(BinOp::EqCmp, test, value)
                                };
                                Ok(PureLowerResult::UnassignedExpression(
                                    self.alloc(block, Exp::new_cond(cond, thn, els)),
                                    thn_slot,
                                    Some(next),
                                ))
                            }
                            (
                                PureLowerResult::UnassignedExpression(els, els_slot, _),
                                PureLowerResult::Empty { .. },
                            ) => Ok(PureLowerResult::UnassignedExpression(
                                els,
                                els_slot,
                                Some(next),
                            )),
                            (PureLowerResult::Empty { .. }, _) => {
                                Err(ViperLowerError::NotYetImplemented {
                                    msg: format!("divergent branches: {otherwise} is empty, and was told to stop at {block}"),
                                    def: self.body.def(),
                                    block_or_inst: Some(otherwise.into()),
                                    span: None,
                                })
                            }
                        }
                    })?;

                    let (exp, slot) = match cont {
                        PureLowerResult::UnassignedExpression(exp, slot, _) => (exp, slot),
                        PureLowerResult::Empty { .. } => todo!(),
                    };

                    self.conditional_continue(stop_at, next, block, slot, exp)?
                }
                mir::Terminator::Call { func, args, destination, target } => {
                    let f = self.function(block, *func, args)?;
                    let f_application = self.alloc(block, f);

                    if let Some(target) = *target {
                        self.conditional_continue(
                            stop_at,
                            target,
                            block,
                            *destination,
                            f_application,
                        )?
                    } else {
                        todo!()
                    }
                }
            },
            None => PureLowerResult::Empty { stopped_before: None },
        };

        self.body[block]
            .instructions()
            .iter()
            .copied()
            .try_rfold(start, |acc, inst| self.pure_wrap_with_instruction(inst, acc))
    }

    pub(super) fn pure_wrap_with_instruction(
        &mut self,
        inst: mir::InstructionId,
        acc: PureLowerResult,
    ) -> Result<PureLowerResult> {
        Ok(match &self.body[inst] {
            mir::Instruction::Assign(x, e) => {
                let exp = self.expr(inst, e)?;
                acc.wrap_in_assignment(self, inst, *x, exp)?
            }
            mir::Instruction::Assertion(_, _) | mir::Instruction::PlaceMention(_) => acc,
            mir::Instruction::Folding(folding) => {
                let unfolding_place = match folding {
                    mir::Folding::Unfold { consume, .. }
                        if !self.pre_unfolded.contains(consume) =>
                    {
                        *consume
                    }
                    _ => return Ok(acc),
                };
                if let Some(s) = self.body.place_ty(unfolding_place).ty_struct() {
                    acc.try_map_exp(|exp| {
                        let place_ref = self.place_to_ref(inst, unfolding_place)?;
                        let pred_acc = PredicateAccessPredicate::new(
                            PredicateAccess::new(
                                mangle::mangled_struct(self.db, s),
                                vec![place_ref],
                            ),
                            self.alloc(inst, PermExp::Wildcard),
                        );

                        Ok(self.alloc(inst, Exp::new_unfolding(pred_acc, exp)))
                    })?
                } else {
                    warn!("no struct found for {:?}", self.body.place_ty(unfolding_place).data());
                    acc
                }
            }
        })
    }

    fn conditional_continue(
        &mut self,
        stop_at: Option<mir::BlockId>,
        next: mir::BlockId,
        block: mir::BlockId,
        place: mir::Place,
        exp: VExprId,
    ) -> Result<PureLowerResult> {
        if stop_at != Some(next) {
            self.pure_block(next, None)?.wrap_in_assignment(self, block, place, exp)
        } else {
            Ok(PureLowerResult::UnassignedExpression(exp, place, Some(next)))
        }
    }

    fn pure_final_block(&mut self, b: mir::BlockId) -> Result<VExprId> {
        match self.pure_block(b, None)? {
            // TODO: Target should be result
            PureLowerResult::UnassignedExpression(exp, _, _) => Ok(exp),
            PureLowerResult::Empty { .. } => Err(ViperLowerError::EmptyBody),
        }
    }
}
