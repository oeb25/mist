use mist_core::{hir, mir, mono::exprs::Field};
use silvers::{
    ast::Declaration,
    expression::{Exp, FieldAccess, PermExp, PredicateAccess, PredicateAccessPredicate, SeqExp},
    program::{AnyLocalVarDecl, Field as VField},
    statement::{Label, Seqn, Stmt},
};

use crate::{gen::VExprId, lower::pure::PureLowerResult, mangle};

use super::{folding::fold_stmt, BodyLower, Result, ViperLowerError};

impl BodyLower<'_> {
    #[tracing::instrument(skip_all)]
    pub fn method_lower(&mut self, entry: mir::BlockId) -> Result<Seqn<VExprId>> {
        self.postdominators = Default::default();
        // TODO: Should we really compute for all entry blocks?
        for bid in self.ib.entry_blocks() {
            self.postdominators.merge(&self.cfg.postdominators(bid));
        }
        self.final_block(entry)
    }

    fn final_block(&mut self, bid: mir::BlockId) -> Result<Seqn<VExprId>> {
        let mut result = self.block(bid, vec![], None)?;
        result.ss.push(Stmt::Label(Label::new("end".to_string(), vec![])));

        for x in self.ib.body_locals() {
            let var = self.local_to_decl(x)?;
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
    ) -> Result<Seqn<VExprId>> {
        self.begin_scope(block, |l| {
            for &inst in block.instructions(l.ib) {
                l.instruction(inst, &mut insts)?;
            }

            match block.terminator(l.ib) {
                Some(t) => match t.kind(l.db) {
                    mir::TerminatorKind::Return => {
                        insts.push(Stmt::Goto { target: "end".to_string() });
                        Ok(Seqn::new(insts, vec![]))
                    }
                    &mir::TerminatorKind::Goto(b) => {
                        if l.should_continue(b, stop_at) {
                            l.block(b, insts, stop_at)
                        } else {
                            Ok(Seqn::new(insts, vec![]))
                        }
                    }
                    mir::TerminatorKind::Quantify(_q, _over, _b) => {
                        Err(ViperLowerError::NotYetImplemented {
                            msg: "lower quantifier in method".to_string(),
                            def: l.ib.item(),
                            block_or_inst: Some(block.into()),
                            span: None,
                        })
                    }
                    mir::TerminatorKind::QuantifyEnd(_) => {
                        todo!();
                    }
                    mir::TerminatorKind::Switch(test, switch) => {
                        let next = l.postdominators[block];

                        let (mut values, otherwise) = switch.values();
                        // TODO: This check is brittle
                        let is_loop = next == otherwise && switch.has_values();
                        if is_loop {
                            let (value, target) = values.next().unwrap();
                            assert_eq!(values.next(), None);
                            let mut body = l.block(target, vec![], Some(block))?;
                            for &inst in block.instructions(l.ib) {
                                l.instruction(inst, &mut body.ss)?;
                            }

                            let cond = match value {
                                1 => l.operand_to_ref(test)?,
                                _ => todo!(), // Exp::new_bin(BinOp::EqCmp, test, value)
                            };

                            let cond =
                                if let Some(&cond) = l.inlined.get(cond) { cond } else { cond };

                            let liveness = mir::analysis::liveness::Liveness::compute(l.db, l.ib);

                            let access_invs = liveness
                                .entry(block.first_body_loc(l.ib))
                                .iter()
                                .map(|s| {
                                    let place = s.place(l.db, l.ib);
                                    let place_ref = l.place_to_ref(place)?;
                                    let (_, post) = l.ty_to_condition(place_ref, place.ty())?;
                                    Ok(post)
                                })
                                .filter_map(|s| s.transpose())
                                .collect::<Result<Vec<_>>>()?;

                            let invs = access_invs
                                .into_iter()
                                .map(Ok)
                                .chain(l.ib.block_invariants(block).iter().map(|bid| {
                                    match l.pure_block(*bid, None)? {
                                        PureLowerResult::UnassignedExpression(exp, _, _) => Ok(exp),
                                        PureLowerResult::Empty { .. } => todo!(),
                                    }
                                }))
                                .collect::<Result<_>>()?;

                            insts.push(Stmt::While { cond, invs, body });

                            if l.should_continue(next, stop_at) {
                                l.block(next, insts, stop_at)
                            } else {
                                Ok(Seqn::new(insts, vec![]))
                            }
                        } else {
                            let mut diverged = false;
                            let otherwise = l.block(otherwise, vec![], Some(next))?;
                            let if_stmt = values.try_fold(otherwise, |els, (value, target)| {
                                if target == next {
                                    diverged = true;
                                }

                                let thn = l.block(target, vec![], Some(next))?;

                                let cond = match value {
                                    1 => l.operand_to_ref(test)?,
                                    _ => todo!(), // Exp::new_bin(BinOp::EqCmp, test, value)
                                };

                                Ok(Seqn::new(vec![Stmt::If { cond, thn, els }], vec![]))
                            })?;

                            insts.push(Stmt::Seqn(if_stmt));

                            if l.should_continue(next, stop_at) && !diverged {
                                l.block(next, insts, stop_at)
                            } else {
                                Ok(Seqn::new(insts, vec![]))
                            }
                        }
                    }
                    mir::TerminatorKind::Call { func, args, destination, target } => {
                        let var = l.place_for_assignment(*destination)?;
                        let f = l.function(*func, args)?;
                        let voided = destination.ty().is_void(l.db);

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
                                let f_application = l.allocs(f);

                                if voided {
                                    insts.push(Stmt::Expression(f_application));
                                } else {
                                    insts
                                        .push(Stmt::LocalVarAssign { lhs: var, rhs: f_application })
                                }
                            }
                        }

                        match *target {
                            Some(target) => {
                                if l.should_continue(target, stop_at) {
                                    l.block(target, insts, stop_at)
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
        })
    }

    #[tracing::instrument(skip_all)]
    fn instruction(
        &mut self,
        inst: mir::InstructionId,
        insts: &mut Vec<Stmt<VExprId>>,
    ) -> Result<()> {
        self.begin_scope(inst, |l| {
            match inst.data(l.ib).clone() {
                mir::Instruction::Assign(t, x) => {
                    let rhs = l.expr(inst, &x)?;
                    l.perform_assignment(t, insts, rhs)?;
                }
                mir::Instruction::NewAdt(t, adt, fields) => {
                    if adt.is_pure(l.db) {
                        let exp = l.pure_new_adt(&adt, inst, &fields)?;
                        l.perform_assignment(t, insts, exp)?;
                        return Ok(());
                    }

                    let base = l.place_to_ref(t)?;
                    let mut new_fields = Vec::with_capacity(fields.len());
                    let mut field_insts = Vec::with_capacity(fields.len());

                    for (af, f) in fields {
                        let ty = l.lower_type(af.ty(l.db))?;
                        let lhs = FieldAccess::new(
                            base,
                            VField::new(mangle::mangled_adt_field(l.db, adt, af), ty.vty.clone()),
                        );
                        new_fields
                            .push(VField::new(mangle::mangled_adt_field(l.db, adt, af), ty.vty));
                        field_insts.push(Stmt::FieldAssign { lhs, rhs: l.operand_to_ref(&f)? });
                    }
                    insts.push(Stmt::NewStmt {
                        lhs: l.place_for_assignment(t)?,
                        fields: new_fields,
                    });
                    insts.extend(field_insts.into_iter());
                    insts.push(Stmt::Fold {
                        acc: {
                            let name = mangle::mangled_adt(l.db, adt);
                            PredicateAccessPredicate::new(
                                PredicateAccess::new(name, vec![base]),
                                l.allocs(PermExp::Full),
                            )
                        },
                    })
                }
                mir::Instruction::Assertion(kind, e) => {
                    let exp = l.expr(inst, &e)?;
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
                    if let Some(stmt) = fold_stmt(l.db, l, folding)? {
                        insts.push(stmt);
                    }
                }
            }
            Ok(())
        })
    }

    fn perform_assignment(
        &mut self,
        t: mir::Place,
        insts: &mut Vec<Stmt<VExprId>>,
        rhs: VExprId,
    ) -> Result<()> {
        match t.projections(self.db) {
            [] => {
                insts.push(Stmt::LocalVarAssign { lhs: self.place_for_assignment(t)?, rhs });
            }
            &[.., mir::Projection::Field(f)] => {
                match f {
                    Field::AdtField(adt, af) => insts.push(Stmt::FieldAssign {
                        lhs: FieldAccess::new(
                            self.place_to_ref(t.parent(self.db).unwrap())?,
                            VField::new(
                                mangle::mangled_adt_field(self.db, adt, af),
                                // TODO: should we respect the extra constraints in such a scenario?
                                self.lower_type(af.ty(self.db))?.vty,
                            ),
                        ),
                        rhs,
                    }),
                    Field::Builtin(_, _) | Field::Undefined => {}
                };
            }
            &[mir::Projection::Index(index, _)] => {
                let idx = self.place_to_ref(index.place(self.db, self.ib))?;
                let seq = self.place_to_ref(t.parent(self.db).unwrap())?;
                let new_rhs = self.allocs(SeqExp::Update { s: seq, idx, elem: rhs });
                let lhs = self.place_for_assignment(t.without_projection(self.db))?;
                insts.push(Stmt::LocalVarAssign { lhs, rhs: new_rhs })
            }
            &[.., mir::Projection::Field(f), mir::Projection::Index(index, _)] => {
                let idx = self.place_to_ref(index.place(self.db, self.ib))?;
                let parent = t.parent(self.db).unwrap();
                let grand_parent = parent.parent(self.db).unwrap();
                let seq = self.place_to_ref(parent)?;
                let new_rhs = self.allocs(SeqExp::Update { s: seq, idx, elem: rhs });
                match f {
                    Field::AdtField(adt, af) => {
                        let lhs = FieldAccess::new(
                            self.place_to_ref(grand_parent)?,
                            VField::new(
                                mangle::mangled_adt_field(self.db, adt, af),
                                // TODO: should we respect the extra constraints in such a scenario?
                                self.lower_type(af.ty(self.db))?.vty,
                            ),
                        );
                        insts.push(Stmt::FieldAssign { lhs, rhs: new_rhs });
                    }
                    Field::Builtin(_, _) | Field::Undefined => {}
                }
            }
            _ => todo!(),
        }
        Ok(())
    }
}
