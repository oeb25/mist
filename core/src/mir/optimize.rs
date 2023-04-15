use std::{cmp::Ordering, collections::HashSet};

use derive_new::new;
use itertools::Itertools;
use la_arena::{Arena, ArenaMap};
use mist_syntax::ast::operators::{BinaryOp, CmpOp, UnaryOp};
use tracing::{debug, info, warn};

use crate::{hir::Literal, mir::FunctionData};

use super::{BlockId, Body, Instruction, InstructionId, MExpr, Slot, SlotId};

pub fn optimize(body: &mut Body) {
    Optimizer::new(body).run();
}

#[derive(new)]
struct Optimizer<'a> {
    body: &'a mut Body,
    #[new(default)]
    assignments: ArenaMap<SlotId, ArenaMap<InstructionId, ()>>,
    #[new(default)]
    reads: ArenaMap<SlotId, ArenaMap<InstructionId, ()>>,
    #[new(default)]
    direct_ref: ArenaMap<SlotId, ArenaMap<SlotId, ()>>,
    #[new(default)]
    direct_lit: ArenaMap<SlotId, HashSet<Literal>>,
    #[new(default)]
    redirect_slot: ArenaMap<SlotId, SlotId>,
    #[new(default)]
    inst_block: ArenaMap<InstructionId, BlockId>,
    #[new(default)]
    live_blocks: ArenaMap<BlockId, ()>,
}

impl Optimizer<'_> {
    fn run(&mut self) {
        for (sid, _) in self.body.slots.iter() {
            self.redirect_slot.insert(sid, sid);
        }

        for _ in 0..6 {
            // info!("iter...");
            if let Some(result) = self.body.result_slot {
                // warn!("resetting result slot {:?}", result);
                self.redirect_slot.insert(result, result);
            }

            self.live_blocks.clear();
            let mut queue = self.body.body_block.into_iter().collect_vec();
            while let Some(bid) = queue.pop() {
                if self.live_blocks.insert(bid, ()).is_some() {
                    continue;
                }
                for inst in self.body.blocks[bid].instructions() {
                    match &self.body[inst] {
                        Instruction::Assign(_, e) => {
                            if let MExpr::Quantifier(_, _, _, b) = e {
                                queue.push(*b)
                            }
                        }
                        Instruction::If(_, t, e) => {
                            queue.push(*t);
                            queue.push(*e);
                        }
                        Instruction::While(_, _, b) => queue.push(*b),
                        Instruction::Assertion(_, _) => {}
                        Instruction::Call(_, _) => {}
                        Instruction::Return => {}
                    }
                }
            }

            self.inst_block.clear();
            self.reads.clear();
            for (b_id, _) in self.live_blocks.iter() {
                for &inst_id in self.body.blocks[b_id].instructions() {
                    self.inst_block.insert(inst_id, b_id);
                    match &mut self.body.instructions[inst_id] {
                        Instruction::Assign(s, expr) => {
                            *s = self.redirect_slot[*s];
                            let s = *s;
                            self.assignments.entry(s).or_default().insert(inst_id, ());

                            *expr = expr.map_slots(|slot| {
                                self.reads.entry(slot).or_default().insert(inst_id, ());
                                self.redirect_slot[slot]
                            });
                        }
                        Instruction::If(c, _, _)
                        | Instruction::While(c, _, _)
                        | Instruction::Assertion(_, c) => {
                            // warn!(
                            //     "performing redirection from {:?} to {:?}",
                            //     c, self.redirect_slot[*c]
                            // );
                            *c = self.redirect_slot[*c];
                            let c = *c;
                            self.reads.entry(c).or_default().insert(inst_id, ());
                        }
                        Instruction::Call(_, args) => {
                            for arg in args {
                                *arg = self.redirect_slot[*arg];
                                let arg = *arg;
                                self.reads.entry(arg).or_default().insert(inst_id, ());
                            }
                        }
                        Instruction::Return => {}
                    }
                }
            }

            self.direct_lit.clear();
            self.direct_ref.clear();
            let mut inline_inst = vec![];

            for (b_id, _) in self.live_blocks.iter() {
                for &inst_id in self.body.blocks[b_id].instructions() {
                    let inst = &mut self.body.instructions[inst_id];
                    match inst {
                        Instruction::Assign(target, e) => {
                            if !self.body.slots[*target].is_result()
                                && self.reads.get(*target).map(|r| r.iter().count() > 0)
                                    != Some(true)
                            {
                                // TODO: Only do this if e has no side effects
                                if !e.contains_side_effects() {
                                    inline_inst.push((inst_id, None));
                                }
                            } else if self.body.slots[*target].is_literal() {
                                inline_inst.push((inst_id, None));
                            } else {
                                match e {
                                    MExpr::Literal(l) => {
                                        self.direct_lit
                                            .entry(*target)
                                            .or_default()
                                            .insert(l.clone());
                                    }
                                    MExpr::Slot(s) => {
                                        // info!(
                                        //     "assignment of {:?} to {:?}",
                                        //     &self.body.slots[*s], &self.body.slots[*target]
                                        // );
                                        self.direct_ref.entry(*target).or_default().insert(*s, ());
                                    }
                                    MExpr::Call(f, args)
                                        if args
                                            .iter()
                                            .all(|a| self.body.slots[*a].is_literal()) =>
                                    {
                                        let args = args
                                            .iter()
                                            .filter_map(|a| self.body.slots[*a].as_literal())
                                            .collect_vec();
                                        let result = match &*self.body.functions[*f] {
                                            FunctionData::BinaryOp(op) => match op {
                                                BinaryOp::LogicOp(_) => todo!(),
                                                BinaryOp::CmpOp(op) => match *op {
                                                    CmpOp::Eq { negated } => None,
                                                    CmpOp::Ord { ordering, strict } => {
                                                        let lhs = args[0].as_int().unwrap();
                                                        let rhs = args[1].as_int().unwrap();
                                                        match ordering {
                                                            Ordering::Less => {
                                                                if strict {
                                                                    Some(Literal::Bool(lhs <= rhs))
                                                                } else {
                                                                    Some(Literal::Bool(lhs < rhs))
                                                                }
                                                            }
                                                            Ordering::Equal => {
                                                                Some(Literal::Bool(lhs == rhs))
                                                            }
                                                            Ordering::Greater => {
                                                                if strict {
                                                                    Some(Literal::Bool(lhs >= rhs))
                                                                } else {
                                                                    Some(Literal::Bool(lhs > rhs))
                                                                }
                                                            }
                                                        }
                                                    }
                                                },
                                                BinaryOp::ArithOp(op) => match op {
                                                    _ => None,
                                                },
                                                BinaryOp::Assignment => None,
                                            },
                                            FunctionData::UnaryOp(op) => match op {
                                                UnaryOp::Not => {
                                                    Some(Literal::Bool(!args[0].as_bool().unwrap()))
                                                }
                                                UnaryOp::Neg => {
                                                    Some(Literal::Int(-args[0].as_int().unwrap()))
                                                }
                                            },
                                            _ => None,
                                        };
                                        if let Some(lit) = result {
                                            *e = MExpr::Literal(lit);
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                        Instruction::If(c, t, e) => {
                            if let Slot::Literal(l) = &self.body.slots[*c] {
                                match l {
                                    Literal::Bool(true) => inline_inst.push((inst_id, Some(*t))),
                                    Literal::Bool(false) => inline_inst.push((inst_id, Some(*e))),
                                    _ => {}
                                }
                            }
                        }
                        Instruction::While(_, _, _) => {}
                        Instruction::Assertion(_, _) => {}
                        Instruction::Call(_, _) => {}
                        Instruction::Return => {}
                    }
                }
            }
            for (inst_id, new_id) in inline_inst {
                let Some(&parent_id) = self.inst_block.get(inst_id) else { continue; };
                let idx = self.body.blocks[parent_id]
                    .instructions
                    .iter()
                    .position(|x| *x == inst_id)
                    .unwrap();
                self.body.blocks[parent_id].instructions.remove(idx);

                if let Some(new_id) = new_id {
                    for (offset, n) in self.body.blocks[new_id]
                        .instructions
                        .clone()
                        .into_iter()
                        .enumerate()
                    {
                        self.body.blocks[parent_id]
                            .instructions
                            .insert(idx + offset, n);
                    }
                }
            }
            let mut updates = vec![];
            for (s, _) in self.body.slots.iter() {
                match (self.direct_lit.get(s), self.direct_ref.get(s)) {
                    (None, None) => {}
                    (None, Some(new_ss)) => {
                        if new_ss.values().count() == 1 {
                            let (new_s, _) = new_ss.iter().next().unwrap();
                            self.redirect_slot.insert(s, new_s);
                        }
                    }
                    (Some(new_ss), None) => {
                        if new_ss.len() == 1 {
                            // warn!("Gotta inline a lit! {:?} becomes {:?}", s, new_ss);
                            let new_s = new_ss.iter().next().unwrap().clone();
                            updates.push((s, Slot::Literal(new_s)));
                        }
                    }
                    (Some(_), Some(_)) => {}
                }
            }
            for (sid, slot) in updates {
                self.redirect_slot.insert(sid, self.body.slots.alloc(slot));
            }

            for (a, &b) in self.redirect_slot.iter() {
                if a != b {
                    // info!("{:?} -> {:?}", &self.body.slots[a], &self.body.slots[b]);
                }
            }
        }
    }
}
