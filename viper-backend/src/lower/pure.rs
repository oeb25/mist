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

use mist_core::mir::analysis::cfg::{self, Cfg};

use super::*;

#[derive(Debug)]
pub struct PureLower<'a> {
    cx: &'a hir::ItemContext,
    body: &'a mir::Body,
    viper_body: &'a mut ViperBody,
    source_map: &'a mut ViperSourceMap,
    cfg: cfg::Cfg,
    postdominance_frontier: cfg::PostdominanceFrontier,
    postdominators: cfg::Postdominators,
    var_refs: ArenaMap<mir::SlotId, VExprId>,
    times_referenced: ArenaMap<mir::SlotId, usize>,
    inlined: ArenaMap<VExprId, VExprId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, derive_more::From)]
enum BlockOrInstruction {
    Block(mir::BlockId),
    Instruction(mir::InstructionId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LowerResult {
    UnassignedExpression(VExprId, mir::SlotId),
    Empty,
}
impl LowerResult {
    fn wrap_in_assignment(
        self,
        lower: &mut PureLower<'_>,
        source: impl Into<BlockOrInstruction>,
        x: SlotId,
        exp: Idx<VExpr>,
    ) -> Result<LowerResult, ViperLowerError> {
        match self {
            LowerResult::UnassignedExpression(body, target) => {
                let inline = match &*lower.viper_body[exp] {
                    _ if lower.times_referenced.get(x) < Some(&2) => true,
                    Exp::Literal(_) | Exp::AbstractLocalVar(_) => true,
                    _ => false,
                };
                if inline {
                    let r = lower.slot_to_ref(x);
                    lower.inlined.insert(r, exp);
                    Ok(self)
                } else {
                    let variable = lower.slot_to_decl(x);
                    Ok(LowerResult::UnassignedExpression(
                        lower.alloc(source, VExpr::new(Exp::new_let(variable, exp, body))),
                        target,
                    ))
                }
            }
            LowerResult::Empty => Ok(LowerResult::UnassignedExpression(exp, x)),
        }
    }
}

impl<'a> PureLower<'a> {
    pub fn new(
        cx: &'a hir::ItemContext,
        body: &'a mir::Body,
        viper_body: &'a mut ViperBody,
        source_map: &'a mut ViperSourceMap,
    ) -> Self {
        let cfg = Cfg::compute(body);
        Self {
            cx,
            body,
            viper_body,
            source_map,
            cfg,
            postdominance_frontier: Default::default(),
            postdominators: Default::default(),
            var_refs: Default::default(),
            times_referenced: Default::default(),
            inlined: Default::default(),
        }
    }

    pub fn lower(&mut self, entry: mir::BlockId) -> Result<VExprId, ViperLowerError> {
        self.postdominance_frontier = self.cfg.postdominance_frontier(entry);
        self.postdominators = self.cfg.postdominators(entry);
        self.final_block(entry)
    }

    pub fn finish(self) {
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
impl<'a> Drop for PureLower<'a> {
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

impl PureLower<'_> {
    fn alloc(&mut self, source: impl Into<BlockOrInstruction>, vexpr: VExpr) -> VExprId {
        let id = self.viper_body.arena.alloc(vexpr);
        match source.into() {
            BlockOrInstruction::Block(_) => {}
            BlockOrInstruction::Instruction(inst_id) => {
                self.source_map.inst_expr.insert(inst_id, id);
                self.source_map.inst_expr_back.insert(id, inst_id);
            }
        }
        id
    }
    fn block(
        &mut self,
        block: mir::BlockId,
        d: Option<mir::BlockId>,
    ) -> Result<LowerResult, ViperLowerError> {
        if Some(block) == d {
            todo!();
        }

        let start = match self.body[block].terminator() {
            Some(t) => match t {
                mir::Terminator::Return => {
                    return Err(ViperLowerError::NotYetImplemented(
                        "return terminator".to_string(),
                    ))
                }
                &mir::Terminator::Goto(next) => {
                    if let Some(d) = d {
                        if self.postdominance_frontier[next].contains(&d) {
                            self.block(next, Some(d))?
                        } else {
                            LowerResult::Empty
                        }
                    } else {
                        self.block(next, None)?
                    }
                }
                mir::Terminator::Switch(test, switch) => {
                    let (mut values, otherwise) = switch.values();
                    let otherwise = self.block(otherwise, Some(block))?;
                    let cont = values.try_fold(otherwise, |els, (value, target)| {
                        match (els, self.block(target, Some(block))?) {
                            (
                                LowerResult::UnassignedExpression(els, els_slot),
                                LowerResult::UnassignedExpression(thn, thn_slot),
                            ) => {
                                if thn_slot != els_slot {
                                    return Err(ViperLowerError::NotYetImplemented(
                                        "divergent branches".to_string(),
                                    ));
                                }
                                let cond = match value {
                                    1 => self.slot_to_ref(*test),
                                    _ => todo!(), // Exp::new_bin(BinOp::EqCmp, test, value)
                                };
                                Ok(LowerResult::UnassignedExpression(
                                    self.alloc(block, VExpr::new(Exp::new_cond(cond, thn, els))),
                                    thn_slot,
                                ))
                            }
                            (
                                LowerResult::UnassignedExpression(els, els_slot),
                                LowerResult::Empty,
                            ) => Ok(LowerResult::UnassignedExpression(els, els_slot)),
                            (LowerResult::Empty, _) => Err(ViperLowerError::NotYetImplemented(
                                "divergent branches".to_string(),
                            )),
                        }
                    })?;

                    let (exp, slot) = match cont {
                        LowerResult::UnassignedExpression(exp, slot) => (exp, slot),
                        LowerResult::Empty => todo!(),
                    };

                    let next = self.postdominators[block];

                    self.conditional_continue(d, next, block, slot, exp)?
                }
                mir::Terminator::Call {
                    func,
                    args,
                    destination,
                    target,
                } => {
                    let f = self.function(*func, args)?;
                    let f_application = self.alloc(block, VExpr::new(f));

                    if let Some(target) = *target {
                        self.conditional_continue(d, target, block, *destination, f_application)?
                    } else {
                        todo!()
                    }
                }
            },
            None => LowerResult::Empty,
        };

        self.body[block]
            .instructions()
            .iter()
            .copied()
            .try_rfold(start, |acc, inst| {
                Ok(match &self.body[inst] {
                    mir::Instruction::Assign(x, e) => {
                        let exp = self.expr(inst, e)?;
                        acc.wrap_in_assignment(self, inst, *x, exp)?
                    }
                    mir::Instruction::Assertion(_, _) => acc,
                })
            })
    }

    fn conditional_continue(
        &mut self,
        d: Option<mir::BlockId>,
        next: mir::BlockId,
        block: mir::BlockId,
        slot: mir::SlotId,
        exp: Idx<VExpr>,
    ) -> Result<LowerResult, ViperLowerError> {
        Ok(if let Some(d) = d {
            if self.postdominance_frontier[next].contains(&d) {
                self.block(next, Some(d))?
                    .wrap_in_assignment(self, block, slot, exp)?
            } else {
                LowerResult::UnassignedExpression(exp, slot)
            }
        } else {
            self.block(next, None)?
                .wrap_in_assignment(self, block, slot, exp)?
        })
    }

    fn slot_to_decl(&self, x: mir::SlotId) -> LocalVarDecl {
        let var = self.slot_to_var(x);
        LocalVarDecl {
            name: var.name,
            typ: var.typ,
        }
    }
    fn slot_to_var(&self, x: mir::SlotId) -> LocalVar {
        LocalVar {
            name: format!("_{}", x.into_raw()),
            typ: VTy::int(),
        }
    }
    fn slot_to_ref(&mut self, s: mir::SlotId) -> VExprId {
        *self.times_referenced.entry(s).or_default() += 1;
        let var = self.slot_to_var(s);
        *self.var_refs.entry(s).or_insert_with(|| {
            let exp = match &self.body[s] {
                mir::Slot::Temp | mir::Slot::Var(_) => {
                    Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(var))
                }
                mir::Slot::Literal(l) => lower_lit(l),
                mir::Slot::Result => Exp::AbstractLocalVar(AbstractLocalVar::Result {
                    typ: VTy::internal_type(),
                }),
            };

            self.viper_body.arena.alloc(VExpr::new(exp))
        })
    }

    fn expr(
        &mut self,
        inst: mir::InstructionId,
        e: &mir::MExpr,
    ) -> Result<VExprId, ViperLowerError> {
        let exp = match e {
            mir::MExpr::Literal(l) => lower_lit(l),
            mir::MExpr::Call(fid, args) => self.function(*fid, args)?,
            mir::MExpr::Field(rcr, f) => match &f.parent {
                hir::FieldParent::Struct(_) => {
                    return Err(ViperLowerError::NotYetImplemented(format!(
                        "lower struct field: {f:?}"
                    )));
                }
                hir::FieldParent::List(_) => match f.name.as_str() {
                    "len" => Exp::Seq(SeqExp::new_length(self.slot_to_ref(*rcr))),
                    _ => {
                        return Err(ViperLowerError::NotYetImplemented(format!(
                            "lower list field: {f:?}"
                        )));
                    }
                },
            },
            mir::MExpr::Struct(_, _) => {
                return Err(ViperLowerError::NotYetImplemented(
                    "lower struct".to_string(),
                ));
            }
            mir::MExpr::Slot(s) => {
                let id = self.slot_to_ref(*s);
                self.source_map.inst_expr.insert(inst, id);
                self.source_map.inst_expr_back.insert(id, inst);
                return Ok(id);
            }
            mir::MExpr::Quantifier(_q_target, q, params, body) => {
                let variables = params
                    .iter()
                    .map(|param| Ok(self.slot_to_decl(*param)))
                    .collect::<Result<_, _>>()?;
                match self.block(*body, None)? {
                    LowerResult::UnassignedExpression(exp, _target) => {
                        // TODO: target should be _q_target
                        let triggers = vec![];
                        match q {
                            hir::Quantifier::Forall => Exp::forall(variables, triggers, exp),
                            hir::Quantifier::Exists => Exp::exists(variables, triggers, exp),
                        }
                    }
                    LowerResult::Empty => todo!(),
                }
            }
            mir::MExpr::BinaryOp(op, l, r) => {
                let op = lower_binop(op).expect("assignment should have been filtered out by now");
                let lhs = self.slot_to_ref(*l);
                let rhs = self.slot_to_ref(*r);
                Exp::new_bin(op, lhs, rhs)
            }
            mir::MExpr::UnaryOp(op, x) => {
                use mist_syntax::ast::operators::UnaryOp;

                let op = match op {
                    UnaryOp::Not => UnOp::Not,
                    UnaryOp::Neg => UnOp::Minus,
                };
                let x = self.slot_to_ref(*x);
                Exp::new_un(op, x)
            }
        };
        Ok(self.alloc(inst, VExpr::new(exp)))
    }

    fn function(
        &mut self,
        fid: mir::FunctionId,
        args: &[mir::SlotId],
    ) -> Result<Exp<VExprId>, ViperLowerError> {
        Ok(match &*self.body[fid] {
            mir::FunctionData::Named(v) => Exp::new_func_app(
                self.cx.var_ident(*v).to_string(),
                args.iter().map(|s| self.slot_to_ref(*s)).collect(),
            ),
            mir::FunctionData::Index => {
                let base = self.slot_to_ref(args[0]);
                let index = self.slot_to_ref(args[1]);
                Exp::Seq(SeqExp::new_index(base, index))
            }
            mir::FunctionData::RangeIndex => {
                let base = self.slot_to_ref(args[0]);
                let index = self.slot_to_ref(args[1]);
                Exp::new_func_app("range_index".to_string(), vec![base, index])
            }
            mir::FunctionData::Range(op) => {
                let (f, args) = match op {
                    mir::RangeKind::FromTo => (
                        "range_from_to",
                        vec![self.slot_to_ref(args[0]), self.slot_to_ref(args[1])],
                    ),
                    mir::RangeKind::From => ("range_from", vec![self.slot_to_ref(args[0])]),
                    mir::RangeKind::To => ("range_to", vec![self.slot_to_ref(args[0])]),
                    mir::RangeKind::Full => ("range_full", vec![]),
                };
                Exp::new_func_app(f.to_string(), args)
            }
            mir::FunctionData::List => Exp::Seq(SeqExp::new_explicit(
                args.iter().map(|s| self.slot_to_ref(*s)).collect(),
            )),
        })
    }

    fn final_block(&mut self, b: mir::BlockId) -> Result<VExprId, ViperLowerError> {
        match self.block(b, None)? {
            // TODO: Target should be result
            LowerResult::UnassignedExpression(exp, _) => Ok(exp),
            LowerResult::Empty => Err(ViperLowerError::EmptyBody),
        }
    }
}
