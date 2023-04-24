use la_arena::ArenaMap;
use mist_core::{hir, mir};
use silvers::{
    ast::Declaration,
    expression::Exp,
    program::AnyLocalVarDecl,
    statement::{Seqn, Stmt},
};

use crate::{
    gen::{VExpr, VExprId},
    lower::pure::PureLowerResult,
};

use super::{BodyLower, ViperLowerError};

impl BodyLower<'_> {
    pub fn method_lower(&mut self, entry: mir::BlockId) -> Result<Seqn<VExprId>, ViperLowerError> {
        self.postdominance_frontier = self.cfg.postdominance_frontier(entry);
        self.postdominators = self.cfg.postdominators(entry);
        self.final_block(entry)
    }

    fn final_block(&mut self, b: mir::BlockId) -> Result<Seqn<VExprId>, ViperLowerError> {
        let mut result = self.block(b, vec![], None)?;

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
            match &self.body[inst] {
                mir::Instruction::Assign(s, x) => {
                    let rhs = self.expr(inst, x)?;
                    // TODO: This number is not correct when we do forward iteration
                    match self.body.reference_to(*s).count() {
                        0 => {
                            // insts.push(Stmt::Expression(rhs));
                            // TODO: We don't need to assign
                            insts.push(Stmt::LocalVarAssign {
                                lhs: self.slot_to_var(*s),
                                rhs,
                            });
                        }
                        _ if self.can_inline(*s, rhs) => {
                            let r = self.slot_to_ref(inst, *s);
                            self.inlined.insert(r, rhs);
                        }
                        _ => {
                            self.times_referenced.entry(*s).or_default();
                            if self.body.slot_ty(*s).is_void(self.db) {
                                insts.push(Stmt::Expression(rhs));
                            } else {
                                insts.push(Stmt::LocalVarAssign {
                                    lhs: self.slot_to_var(*s),
                                    rhs,
                                });
                            }
                        }
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
            }
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
                        let body = self.block(target, vec![], Some(block))?;

                        let cond = match value {
                            1 => self.operand_to_ref(block, test),
                            _ => todo!(), // Exp::new_bin(BinOp::EqCmp, test, value)
                        };
                        let invs = self
                            .body
                            .block_invariants(block)
                            .iter()
                            .map(|bid| match self.pure_block(*bid, None)? {
                                PureLowerResult::UnassignedExpression(exp, _, _) => Ok(exp),
                                PureLowerResult::Empty { .. } => todo!(),
                            })
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
                    self.times_referenced.entry(*destination).or_default();
                    let var = self.slot_to_var(*destination);
                    let f = self.function(block, *func, args)?;
                    let voided = self.body.slot_ty(*destination).is_void(self.db);

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
                            let f_application = self.alloc(block, VExpr::new(f));

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
}
