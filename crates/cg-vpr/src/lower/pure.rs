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

use mist_core::{
    hir, mir,
    mono::types::{Adt, AdtField},
};
use silvers::expression::{Exp, QuantifierExp};

use crate::{gen::VExprId, mangle};

use super::{folding::folding_expr, BodyLower, Result, ViperLowerError};

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
        source: impl Into<mir::BlockOrInstruction> + Copy,
        x: mir::Place,
        exp: VExprId,
    ) -> Result<PureLowerResult> {
        match self {
            PureLowerResult::UnassignedExpression(body, target, stopped_before) => {
                if lower.can_inline(x, exp) {
                    let r = lower.place_to_ref(x)?;
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

    pub(super) fn try_map_exp(
        self,
        mut f: impl FnMut(VExprId) -> Result<VExprId>,
    ) -> Result<PureLowerResult> {
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
            return Err(ViperLowerError::NotYetImplemented {
                msg: "tried to lower a block which should be stopped at".to_string(),
                def: self.ib.item(),
                block_or_inst: Some(block.into()),
                span: None,
            });
        }
        self.begin_scope(block, |l| {
            let start = match block.terminator(l.ib) {
                Some(t) => match t.kind(l.db) {
                    mir::TerminatorKind::Return => {
                        return Err(ViperLowerError::NotYetImplemented {
                            msg: "return terminator".to_string(),
                            def: l.ib.item(),
                            block_or_inst: Some(block.into()),
                            span: None,
                        })
                    }
                    mir::TerminatorKind::Quantify(q, over, next) => match l
                        .pure_block(*next, None)?
                    {
                        PureLowerResult::UnassignedExpression(exp, place, stopped_before) => {
                            for s in over {
                                l.internally_bound_slots.insert(*s, ());
                            }

                            let variables =
                                over.iter().map(|s| l.slot_to_decl(*s)).collect::<Result<_>>()?;
                            let triggers = vec![];

                            PureLowerResult::UnassignedExpression(
                                l.allocs(match q {
                                    hir::Quantifier::Forall => {
                                        QuantifierExp::Forall { variables, triggers, exp }
                                    }
                                    hir::Quantifier::Exists => {
                                        QuantifierExp::Exists { variables, triggers, exp }
                                    }
                                }),
                                // TODO
                                place,
                                // l.ib.result_slot().unwrap().into(),
                                stopped_before,
                            )
                        }
                        PureLowerResult::Empty { .. } => {
                            return Err(ViperLowerError::NotYetImplemented {
                                msg: "quantifier with empty result".into(),
                                def: l.ib.item(),
                                block_or_inst: Some(block.into()),
                                span: None,
                            })
                        }
                    },
                    mir::TerminatorKind::QuantifyEnd(next) => {
                        PureLowerResult::Empty { stopped_before: Some(*next) }
                    }
                    &mir::TerminatorKind::Goto(next) => {
                        if stop_at == Some(next) {
                            PureLowerResult::Empty { stopped_before: Some(next) }
                        } else {
                            l.pure_block(next, stop_at)?
                        }
                    }
                    mir::TerminatorKind::Switch(test, switch) => {
                        let next = if let Some(next) = l.postdominators.get(block) {
                            next
                        } else {
                            return Err(ViperLowerError::NotYetImplemented {
                                msg: format!("block {block} did not have a postdominator"),
                                def: l.ib.item(),
                                block_or_inst: Some(block.into()),
                                span: None,
                            });
                        };

                        let (mut values, otherwise) = switch.values();
                        let otherwise_result = l.pure_block(otherwise, Some(next))?;
                        let cont = values.try_fold(otherwise_result, |els, (value, target)| {
                            match (els, l.pure_block(target, Some(next))?) {
                                (
                                    PureLowerResult::UnassignedExpression(els, els_slot, _),
                                    PureLowerResult::UnassignedExpression(thn, thn_slot, _),
                                ) => {
                                    if thn_slot != els_slot {
                                        return Err(ViperLowerError::NotYetImplemented {
                                            msg: "divergent branches".to_string(),
                                            def: l.ib.item(),
                                            block_or_inst: Some(block.into()),
                                            span: None,
                                        });
                                    }
                                    let cond = match value {
                                        1 => l.operand_to_ref(test)?,
                                        _ => todo!(), // Exp::new_bin(BinOp::EqCmp, test, value)
                                    };
                                    Ok(PureLowerResult::UnassignedExpression(
                                        l.alloc(block, Exp::new_cond(cond, thn, els)),
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
                                    let msg = format!(
                                        "divergent branches: \
                                            {otherwise} is empty, and was told to stop at {block}"
                                    );

                                    Err(ViperLowerError::NotYetImplemented {
                                        msg,
                                        def: l.ib.item(),
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

                        l.conditional_continue(stop_at, next, block, slot, exp)?
                    }
                    mir::TerminatorKind::Call { func, args, destination, target } => {
                        let f = l.function(*func, args)?;
                        let f_application = l.alloc(block, f);

                        if let Some(target) = *target {
                            l.conditional_continue(
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

            block
                .instructions(l.ib)
                .iter()
                .copied()
                .try_rfold(start, |acc, inst| l.pure_wrap_with_instruction(inst, acc))
        })
    }

    pub(super) fn pure_wrap_with_instruction(
        &mut self,
        inst: mir::InstructionId,
        acc: PureLowerResult,
    ) -> Result<PureLowerResult> {
        Ok(match inst.data(self.ib) {
            mir::Instruction::Assign(x, e) => {
                let exp = self.expr(inst, e)?;
                acc.wrap_in_assignment(self, inst, *x, exp)?
            }
            mir::Instruction::NewAdt(x, adt, fields) => {
                let exp = self.pure_new_adt(adt, inst, fields)?;
                acc.wrap_in_assignment(self, inst, *x, exp)?
            }
            mir::Instruction::Assertion(_, _) | mir::Instruction::PlaceMention(_) => acc,
            mir::Instruction::Folding(folding) => folding_expr(self.db, self, acc, *folding)?,
        })
    }

    pub(super) fn pure_new_adt(
        &mut self,
        adt: &Adt,
        inst: mir::InstructionId,
        fields: &[(AdtField, mir::Operand)],
    ) -> Result<VExprId> {
        if !adt.is_pure(self.db) {
            return Err(ViperLowerError::NotYetImplemented {
                msg: "non-pure struct initialization in pure context".to_string(),
                def: self.ib.item(),
                block_or_inst: Some(inst.into()),
                span: None,
            });
        }
        let exp = Exp::FuncApp {
            funcname: mangle::mangled_adt(self.db, *adt) + "_init",
            args: fields.iter().map(|(_, op)| self.operand_to_ref(op)).collect::<Result<_>>()?,
        };
        Ok(self.alloc(inst, exp))
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
