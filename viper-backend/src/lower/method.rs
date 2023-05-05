use itertools::Itertools;
use la_arena::ArenaMap;
use mist_core::{
    hir,
    mir::{self, Projection},
};
use silvers::{
    ast::Declaration,
    expression::{
        AccessPredicate, Exp, FieldAccess, PermExp, PredicateAccess, PredicateAccessPredicate,
        SeqExp,
    },
    program::{AnyLocalVarDecl, Field},
    statement::{Seqn, Stmt},
};
use tracing::{info, warn};

use crate::{gen::VExprId, lower::pure::PureLowerResult};

use super::{BodyLower, ViperLowerError};

impl BodyLower<'_> {
    pub fn method_lower(&mut self, entry: mir::BlockId) -> Result<Seqn<VExprId>, ViperLowerError> {
        // self.postdominance_frontier = self.cfg.postdominance_frontier(entry);
        self.postdominance_frontier = Default::default();
        for bid in self.body.entry_blocks() {
            self.postdominance_frontier
                .merge(&self.cfg.postdominance_frontier(bid));
        }
        self.postdominators = Default::default();
        for bid in self.body.entry_blocks() {
            self.postdominators.merge(&self.cfg.postdominators(bid));
        }
        self.final_block(entry)
    }

    fn final_block(&mut self, bid: mir::BlockId) -> Result<Seqn<VExprId>, ViperLowerError> {
        let mut result = self.block(bid, vec![], None)?;

        let mut slots_seen = ArenaMap::new();

        // TODO: This is quite excessive. Traversing the generated Seqn might be
        // better
        for s in self.body.slots() {
            slots_seen.insert(s, ());
        }

        for to_remove in self
            .body
            .params()
            .iter()
            .copied()
            .chain(self.body.result_slot())
            .chain(self.internally_bound_slots.iter().map(|(s, _)| s))
        {
            slots_seen.remove(to_remove);
        }

        for (x, _) in slots_seen.iter() {
            let var = self.slot_to_decl(x);
            result
                .scoped_seqn_declarations
                .push(Declaration::LocalVar(AnyLocalVarDecl::LocalVarDecl(var)));
        }
        Ok(result)
    }
}

impl BodyLower<'_> {
    fn should_continue(&self, next: mir::BlockId, stop_at: Option<mir::BlockId>) -> bool {
        match stop_at {
            Some(stop_at) => next != stop_at,
            None => true,
        }

        // TODO: This was the old approach, but perhaps the above is totalyl correct?
        // if let Some(d) = stop_at {
        //     !self.postdominance_frontier[next].contains(&d)
        // } else {
        //     true
        // }
    }

    fn block(
        &mut self,
        block: mir::BlockId,
        mut insts: Vec<Stmt<VExprId>>,
        stop_at: Option<mir::BlockId>,
    ) -> Result<Seqn<VExprId>, ViperLowerError> {
        for &inst in self.body[block].instructions() {
            self.instruction(inst, &mut insts)?;
        }

        match self.body[block].terminator() {
            Some(t) => match t {
                mir::Terminator::Return => Ok(Seqn::new(insts, vec![])),
                &mir::Terminator::Goto(b) => {
                    if self.should_continue(b, stop_at) {
                        self.block(b, insts, stop_at)
                    } else {
                        Ok(Seqn::new(insts, vec![]))
                    }
                }
                mir::Terminator::Quantify(q, over, b) => {
                    todo!();
                }
                mir::Terminator::QuantifyEnd(_) => {
                    todo!();
                }
                mir::Terminator::Switch(test, switch) => {
                    let next = self.postdominators[block];

                    let (mut values, otherwise) = switch.values();
                    // TODO: This check is brittle
                    let is_loop = next == otherwise && switch.has_values();
                    if is_loop {
                        let (value, target) = values.next().unwrap();
                        assert_eq!(values.next(), None);
                        let mut body = self.block(target, vec![], Some(block))?;
                        for &inst in self.body[block].instructions() {
                            self.instruction(inst, &mut body.ss)?;
                        }

                        let cond = match value {
                            1 => self.operand_to_ref(block, test),
                            _ => todo!(), // Exp::new_bin(BinOp::EqCmp, test, value)
                        };

                        let cond = if let Some(&cond) = self.inlined.get(cond) {
                            cond
                        } else {
                            cond
                        };

                        let liveness = mir::analysis::liveness::Liveness::compute(self.body);

                        let access_invs = liveness
                            .entry(block)
                            .iter()
                            .filter_map(|s| {
                                if let Some(t) = self.cx.ty_struct(self.body.place_ty(s.into())) {
                                    let name = t.name(self.db);
                                    let place_ref = self.place_to_ref(block, s.into());
                                    let acc = PredicateAccessPredicate::new(
                                        PredicateAccess::new(name.to_string(), vec![place_ref]),
                                        self.alloc(block, PermExp::Full),
                                    );
                                    Some(self.alloc(block, AccessPredicate::Predicate(acc)))
                                } else {
                                    None
                                }
                            })
                            .collect_vec();

                        let invs = access_invs
                            .into_iter()
                            .map(Ok)
                            .chain(self.body.block_invariants(block).iter().map(|bid| {
                                match self.pure_block(*bid, None)? {
                                    PureLowerResult::UnassignedExpression(exp, _, _) => Ok(exp),
                                    PureLowerResult::Empty { .. } => todo!(),
                                }
                            }))
                            .collect::<Result<_, _>>()?;

                        insts.push(Stmt::While { cond, invs, body });
                    } else {
                        let otherwise = self.block(otherwise, vec![], Some(next))?;
                        let if_stmt = values.try_fold(otherwise, |els, (value, target)| {
                            let thn = self.block(target, vec![], Some(next))?;

                            let cond = match value {
                                1 => self.operand_to_ref(block, test),
                                _ => todo!(), // Exp::new_bin(BinOp::EqCmp, test, value)
                            };

                            Ok(Seqn::new(vec![Stmt::If { cond, thn, els }], vec![]))
                        })?;

                        insts.push(Stmt::Seqn(if_stmt));
                    }

                    if self.should_continue(next, stop_at) {
                        self.block(next, insts, stop_at)
                    } else {
                        Ok(Seqn::new(insts, vec![]))
                    }
                }
                mir::Terminator::Call {
                    func,
                    args,
                    destination,
                    target,
                } => {
                    let var = self.place_for_assignment(*destination);
                    let f = self.function(block, *func, args)?;
                    let voided =
                        self.cx[self.body.place_ty(*destination).strip_ghost(self.cx)].is_void();

                    match f {
                        Exp::FuncApp { funcname, args } => {
                            if voided {
                                insts.push(Stmt::MethodCall {
                                    method_name: funcname,
                                    args,
                                    targets: vec![],
                                })
                            } else {
                                insts.push(Stmt::MethodCall {
                                    method_name: funcname,
                                    args,
                                    targets: vec![var],
                                })
                            }
                        }
                        _ => {
                            let f_application = self.alloc(block, f);

                            if voided {
                                insts.push(Stmt::Expression(f_application));
                            } else {
                                insts.push(Stmt::LocalVarAssign {
                                    lhs: var,
                                    rhs: f_application,
                                })
                            }
                        }
                    }

                    match *target {
                        Some(target) => {
                            if self.should_continue(target, stop_at) {
                                self.block(target, insts, stop_at)
                            } else {
                                Ok(Seqn::new(insts, vec![]))
                            }
                        }
                        None => Ok(Seqn::new(insts, vec![])),
                    }
                }
            },
            None => Ok(Seqn::new(insts, vec![])),
        }
    }

    fn instruction(
        &mut self,
        inst: mir::InstructionId,
        insts: &mut Vec<Stmt<VExprId>>,
    ) -> Result<(), ViperLowerError> {
        match &self.body[inst] {
            mir::Instruction::Assign(s, x) => {
                let rhs = self.expr(inst, x)?;
                match &self.body[s.projection] {
                    [] => {
                        info!("lowering without projection (1)");
                        insts.push(Stmt::LocalVarAssign {
                            lhs: self.place_for_assignment(*s),
                            rhs,
                        });
                    }
                    [Projection::Field(f, ty)] => {
                        info!("lowering with projection (2)");
                        insts.push(Stmt::FieldAssign {
                            lhs: FieldAccess::new(
                                self.place_to_ref(inst, s.slot.into()),
                                Field::new(
                                    f.name.to_string(),
                                    // TODO: should we respect the extra constraints in such a scenario?
                                    self.lower_type(*ty).vty,
                                ),
                            ),
                            rhs,
                        });
                    }
                    [Projection::Index(index, _)] => {
                        let idx = self.place_to_ref(inst, (*index).into());
                        let seq = self.place_to_ref(inst, s.parent(self.body));
                        let new_rhs = self.alloc(
                            inst,
                            SeqExp::Update {
                                s: seq,
                                idx,
                                elem: rhs,
                            },
                        );
                        let lhs = self.place_for_assignment(s.without_projection());
                        insts.push(Stmt::LocalVarAssign { lhs, rhs: new_rhs })
                    }
                    [Projection::Field(f, ty), Projection::Index(index, _)] => {
                        let idx = self.place_to_ref(inst, (*index).into());
                        let seq = self.place_to_ref(inst, s.parent(self.body));
                        let new_rhs = self.alloc(
                            inst,
                            SeqExp::Update {
                                s: seq,
                                idx,
                                elem: rhs,
                            },
                        );
                        let lhs = FieldAccess::new(
                            self.place_to_ref(inst, s.slot.into()),
                            Field::new(
                                f.name.to_string(),
                                // TODO: should we respect the extra constraints in such a scenario?
                                self.lower_type(*ty).vty,
                            ),
                        );
                        insts.push(Stmt::FieldAssign { lhs, rhs: new_rhs });
                    }
                    _ => todo!(),
                }
            }
            mir::Instruction::Assertion(kind, e) => {
                let exp = self.expr(inst, e)?;
                let stmt = match kind {
                    hir::AssertionKind::Assert => Stmt::Assert { exp },
                    hir::AssertionKind::Assume => Stmt::Assume { exp },
                    hir::AssertionKind::Inhale => Stmt::Inhale { exp },
                    hir::AssertionKind::Exhale => Stmt::Exhale { exp },
                };
                insts.push(stmt);
            }
            mir::Instruction::PlaceMention(_) => {}
            mir::Instruction::Folding(folding) => {
                let place = match folding {
                    mir::Folding::Fold { into, .. } => *into,
                    mir::Folding::Unfold { consume, .. } => *consume,
                };
                if let Some(s) = self.cx.ty_struct(self.body.place_ty(place)) {
                    let name = s.name(self.db);
                    let place_ref = self.place_to_ref(inst, place);
                    let acc = PredicateAccessPredicate::new(
                        PredicateAccess::new(name.to_string(), vec![place_ref]),
                        self.alloc(inst, PermExp::Full),
                    );

                    insts.push(match folding {
                        mir::Folding::Fold { .. } => Stmt::Fold { acc },
                        mir::Folding::Unfold { .. } => Stmt::Unfold { acc },
                    });
                } else {
                    warn!(
                        "no struct found for {:?}",
                        self.cx[self.body.place_ty(place)]
                    );
                }
            }
        }
        Ok(())
    }
}
