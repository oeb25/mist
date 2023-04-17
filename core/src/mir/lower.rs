use std::mem;

use derive_new::new;
use hir::ItemSourceMap;
use itertools::Itertools;
use mist_syntax::ast::operators::BinaryOp;

use crate::{
    hir::{
        self, pretty, Else, ExprData, ExprIdx, IfExpr, Program, Statement, StatementData,
        VariableIdx,
    },
    typecheck::ItemContext,
};

use super::{
    Block, BlockId, Body, BodySourceMap, Function, FunctionData, FunctionId, Instruction,
    InstructionId, MExpr, RangeKind, Slot, SlotId, SwitchTargets, Terminator,
};

pub fn lower_program(
    db: &dyn crate::Db,
    program: Program,
) -> Vec<(hir::Item, ItemContext, ItemSourceMap, Body, BodySourceMap)> {
    program.items(db).iter().filter_map(|item| {
        let Some(item) = hir::item(db, program, item.clone()) else { return None; };
        let Some((cx, item_source_map)) = hir::item_lower(db, program, item) else { return None; };
        let (mir, mir_source_map) = lower_item(db, cx.clone());
        // println!("{}", item_mir.serialize(db, program, &cx))
        Some((item, cx, item_source_map, mir, mir_source_map))
    }).collect()
}

pub fn lower_item(db: &dyn crate::Db, cx: ItemContext) -> (Body, BodySourceMap) {
    let mut lower = MirLower::new(db, &cx);

    for param in cx.params().iter() {
        lower.alloc_slot(Slot::from_var(param.name));
    }

    for cond in cx.conditions() {
        match cond {
            hir::Condition::Requires(es) => {
                for e in es {
                    let slot = lower.alloc_tmp();
                    let entry_bid = lower.body.blocks.alloc(Default::default());
                    lower.expr(*e, entry_bid, None, Some(slot));
                    lower.body.requires.push(entry_bid);
                }
            }
            hir::Condition::Ensures(es) => {
                for e in es {
                    let slot = lower.alloc_tmp();
                    let entry_bid = lower.body.blocks.alloc(Default::default());
                    lower.expr(*e, entry_bid, None, Some(slot));
                    lower.body.ensures.push(entry_bid);
                }
            }
        }
    }

    if let Some(body) = cx.body_expr() {
        let return_slot = lower.alloc_slot(Slot::Result);
        let body_bid = lower.body.blocks.alloc(Default::default());
        lower.expr(body, body_bid, None, Some(return_slot));
        lower.body.body_block = Some(body_bid);
    }

    lower.finish()
}

#[derive(new)]
struct MirLower<'a> {
    db: &'a dyn crate::Db,
    cx: &'a ItemContext,

    #[new(default)]
    body: Body,
    #[new(default)]
    source_map: BodySourceMap,
}

impl MirLower<'_> {
    fn alloc_tmp(&mut self) -> SlotId {
        self.alloc_slot(Slot::default())
    }
    fn alloc_slot(&mut self, slot: Slot) -> SlotId {
        match &slot {
            Slot::Temp | Slot::Literal(_) => self.body.slots.alloc(slot),
            Slot::Var(var) => {
                let var = *var;
                let id = self.body.slots.alloc(slot);
                self.source_map.var_map.insert(var, id);
                id
            }
            Slot::Result => {
                if let Some(id) = self.body.result_slot {
                    id
                } else {
                    let id = self.body.slots.alloc(slot);
                    self.body.result_slot = Some(id);
                    id
                }
            }
        }
    }
    fn alloc_instruction(
        &mut self,
        expr: Option<ExprIdx>,
        bid: BlockId,
        instruction: Instruction,
    ) -> InstructionId {
        let id = self.body.instructions.alloc(instruction);
        self.body.blocks[bid].instructions.push(id);
        if let Some(expr) = expr {
            self.source_map
                .expr_instr_map
                .entry(expr)
                .or_default()
                .push(id);
        }
        id
    }
    fn alloc_block(&mut self, expr: Option<ExprIdx>, block: Block) -> BlockId {
        let id = self.body.blocks.alloc(block);
        if let Some(expr) = expr {
            self.source_map.expr_block_map.insert(expr, id);
        }
        id
    }
    fn alloc_function(&mut self, function: Function) -> FunctionId {
        self.body.functions.alloc(function)
    }
    fn var_slot(&self, var: VariableIdx) -> SlotId {
        self.source_map.var_map[&var]
    }
    fn finish(self) -> (Body, BodySourceMap) {
        (self.body, self.source_map)
    }
}
impl MirLower<'_> {
    // fn expr_to_block(&mut self, expr: ExprIdx, dest: Option<SlotId>) -> BlockId {
    //     let bid = self.body.blocks.alloc(Default::default());

    //     bid

    //     // self.blocked(Some(expr), |this| match &this.cx.expr(expr).data {
    //     //     ExprData::Block(block) => {
    //     //         for stmt in &block.stmts {
    //     //             this.stmt(stmt);
    //     //         }
    //     //         if let Some(tail) = block.tail_expr {
    //     //             let dest = this.expr(tail, dest);
    //     //             Some(dest)
    //     //         } else {
    //     //             dest
    //     //         }
    //     //     }
    //     //     _ => Some(this.expr(expr, dest)),
    //     // })
    // }
    fn block(
        &mut self,
        block: &hir::Block,
        mut bid: BlockId,
        target: Option<BlockId>,
        dest: Option<SlotId>,
    ) -> BlockId {
        for stmt in &block.stmts {
            bid = self.stmt(bid, None, stmt);
        }
        if let Some(tail) = block.tail_expr {
            self.expr(tail, bid, target, dest)
        } else {
            bid
        }
    }
    fn stmt(&mut self, mut bid: BlockId, target: Option<BlockId>, stmt: &Statement) -> BlockId {
        match &stmt.data {
            StatementData::Expr(expr) => self.expr(*expr, bid, target, None),
            StatementData::Let {
                variable,
                explicit_ty: _,
                initializer,
            } => {
                let dest = self.alloc_slot(Slot::from_var(variable.idx()));
                self.expr(*initializer, bid, target, Some(dest))
            }
            StatementData::While {
                expr,
                invariants,
                decreases,
                body,
            } => {
                let cond_block = self.body.blocks.alloc(Default::default());
                assert_ne!(bid, cond_block);
                self.body.blocks[bid].set_terminator(Terminator::Goto(cond_block));

                let cond_slot = self.alloc_tmp();
                bid = self.expr(*expr, cond_block, None, Some(cond_slot));

                let invariants: Vec<_> = invariants
                    .iter()
                    .flatten()
                    .map(|inv| {
                        let inv_block = self.body.blocks.alloc(Default::default());
                        let inv_result = self.alloc_tmp();
                        self.expr(*inv, inv_block, None, Some(inv_result));
                        inv_block
                    })
                    .collect();

                let body_bid = self.body.blocks.alloc(Default::default());
                let body_bid_last = self.block(body, body_bid, None, None);

                let exit_bid = self.body.blocks.alloc(Default::default());

                assert_ne!(body_bid_last, cond_block);
                self.body.blocks[body_bid_last].set_terminator(Terminator::Goto(cond_block));
                self.body.blocks[bid].set_terminator(Terminator::Switch(
                    cond_slot,
                    SwitchTargets::new([(1, body_bid)], exit_bid),
                ));

                // TODO: Annotate the invariants somewhere
                exit_bid
            }
            StatementData::Assertion { kind, exprs } => {
                for expr in exprs {
                    let dest = self.alloc_tmp();
                    bid = self.expr(*expr, bid, None, Some(dest));
                    self.alloc_instruction(None, bid, Instruction::Assertion(kind.clone(), dest));
                }
                bid
            }
        }
    }
    fn assign(
        &mut self,
        bid: BlockId,
        source: Option<ExprIdx>,
        dest: Option<SlotId>,
        expr: MExpr,
    ) -> SlotId {
        let dest = dest.unwrap_or_else(|| self.alloc_tmp());
        self.alloc_instruction(source, bid, Instruction::Assign(dest, expr));
        dest
    }
    fn expr(
        &mut self,
        expr: ExprIdx,
        mut bid: BlockId,
        target: Option<BlockId>,
        dest: Option<SlotId>,
    ) -> BlockId {
        match &self.cx.expr(expr).data {
            ExprData::Literal(l) => {
                let l_slot = self.alloc_slot(Slot::Literal(l.clone()));
                if let Some(dest) = dest {
                    self.assign(bid, Some(expr), Some(dest), MExpr::Slot(l_slot));
                    bid
                } else {
                    // l_slot
                    bid
                }
            }
            ExprData::Ident(var) => {
                let var_slot = self.var_slot(var.idx());
                if let Some(dest) = dest {
                    self.assign(bid, Some(expr), Some(dest), MExpr::Slot(var_slot));
                    bid
                } else {
                    // var_slot
                    bid
                }
            }
            ExprData::Block(block) => {
                let next_bid = self.body.blocks.alloc(Default::default());
                assert_ne!(bid, next_bid);
                self.body.blocks[bid].set_terminator(Terminator::Goto(next_bid));
                // self.body.blocks[bid].set_terminator(Terminator::Goto(next_bid));
                self.block(block, next_bid, target, dest)
            }
            ExprData::Field {
                expr: base,
                field_name: _,
                field,
            } => {
                if let Some(field) = field {
                    let tmp = self.alloc_tmp();
                    let next_bid = self.expr(*base, bid, None, Some(tmp));
                    self.assign(bid, Some(expr), dest, MExpr::Field(tmp, field.clone()));
                    next_bid
                } else {
                    todo!()
                }
            }
            ExprData::Struct {
                struct_declaration,
                struct_span: _,
                fields,
            } => {
                let mut operands = vec![];

                for f in fields {
                    let tmp = self.alloc_tmp();
                    bid = self.expr(f.value, bid, None, Some(tmp));
                    operands.push((f.decl.clone(), tmp));
                }

                self.assign(
                    bid,
                    Some(expr),
                    dest,
                    MExpr::Struct(*struct_declaration, operands),
                );
                bid
            }
            ExprData::Missing => bid,
            ExprData::If(it) => self.if_expr(it, bid, target, dest, expr),
            ExprData::Call {
                expr: f_expr,
                args: input_args,
            } => {
                let (func, mut args) = self.expr_to_function(*f_expr);

                for arg in input_args {
                    let tmp = self.alloc_tmp();
                    bid = self.expr(*arg, bid, None, Some(tmp));
                    args.push(tmp);
                }

                let destination = dest.unwrap_or_else(|| self.alloc_tmp());
                let next_bid = target.unwrap_or_else(|| self.body.blocks.alloc(Default::default()));
                self.body.blocks[bid].set_terminator(Terminator::Call {
                    func,
                    args,
                    destination,
                    target: Some(next_bid),
                });
                next_bid
            }
            ExprData::Unary { op, inner } => {
                let arg = self.alloc_tmp();
                bid = self.expr(*inner, bid, None, Some(arg));
                self.assign(bid, Some(expr), dest, MExpr::UnaryOp(*op, arg));
                bid
            }
            ExprData::Bin { lhs, op, rhs } => {
                if let BinaryOp::Assignment = op {
                    // TODO: lhs should really be computed in a lhs fashion
                    let left = self.alloc_tmp();
                    let right = self.alloc_tmp();
                    bid = self.expr(*lhs, bid, None, Some(left));
                    bid = self.expr(*rhs, bid, None, Some(right));

                    self.assign(bid, Some(expr), Some(left), MExpr::Slot(right));
                    bid
                } else {
                    let left = self.alloc_tmp();
                    let right = self.alloc_tmp();
                    bid = self.expr(*lhs, bid, None, Some(left));
                    bid = self.expr(*rhs, bid, None, Some(right));
                    self.assign(bid, Some(expr), dest, MExpr::BinaryOp(*op, left, right));
                    bid
                }
            }
            ExprData::Ref { is_mut, expr } => todo!(),
            ExprData::Index { base, index } => {
                let f = match &self.cx.expr(*index).ty.strip_ghost(self.db).data(self.db) {
                    hir::TypeData::Range(_) => FunctionData::RangeIndex,
                    hir::TypeData::Primitive(hir::Primitive::Int) => FunctionData::Index,
                    ty => todo!("tried to index with {ty:?}"),
                };
                let base_s = self.alloc_tmp();
                bid = self.expr(*base, bid, None, Some(base_s));
                let index_s = self.alloc_tmp();
                bid = self.expr(*index, bid, None, Some(index_s));
                let func = self.alloc_function(Function::new(f));

                let destination = dest.unwrap_or_else(|| self.alloc_tmp());
                let next_bid = target.unwrap_or_else(|| self.body.blocks.alloc(Default::default()));
                assert_ne!(bid, next_bid);
                self.body.blocks[bid].set_terminator(Terminator::Call {
                    func,
                    args: vec![base_s, index_s],
                    destination,
                    target: Some(next_bid),
                });
                next_bid
            }
            ExprData::List { elems } => {
                let elems = elems
                    .iter()
                    .map(|e| {
                        let elem = self.alloc_tmp();
                        bid = self.expr(*e, bid, None, Some(elem));
                        elem
                    })
                    .collect();
                let func = self.alloc_function(Function::new(FunctionData::List));

                let destination = dest.unwrap_or_else(|| self.alloc_tmp());
                let next_bid = target.unwrap_or_else(|| self.body.blocks.alloc(Default::default()));
                assert_ne!(bid, next_bid);
                self.body.blocks[bid].set_terminator(Terminator::Call {
                    func,
                    args: elems,
                    destination,
                    target: Some(next_bid),
                });
                next_bid
            }
            ExprData::Quantifier {
                quantifier,
                params,
                expr: q_expr,
            } => {
                let q_dest = self.alloc_tmp();
                let q_body = self.body.blocks.alloc(Default::default());
                self.expr(*q_expr, q_body, None, Some(q_dest));
                let params = params
                    .iter()
                    .map(|param| self.alloc_slot(Slot::from_var(param.name)))
                    .collect();
                let mexpr = MExpr::Quantifier(q_dest, *quantifier, params, q_body);

                self.assign(bid, Some(expr), dest, mexpr);
                bid
            }
            ExprData::Result => {
                if let Some(dest) = dest {
                    let result_slot = self.alloc_slot(Slot::Result);
                    self.assign(bid, Some(expr), Some(dest), MExpr::Slot(result_slot));
                }
                bid
            }
            ExprData::Range { lhs, rhs } => {
                let kind = match (lhs, rhs) {
                    (None, None) => RangeKind::Full,
                    (None, Some(_)) => RangeKind::To,
                    (Some(_), None) => RangeKind::From,
                    (Some(_), Some(_)) => RangeKind::FromTo,
                };
                let function = self.alloc_function(Function::new(FunctionData::Range(kind)));

                let args = [lhs, rhs]
                    .into_iter()
                    .flatten()
                    .map(|&a| {
                        let s = self.alloc_tmp();
                        bid = self.expr(a, bid, None, Some(s));
                        s
                    })
                    .collect();

                self.assign(bid, Some(expr), dest, MExpr::Call(function, args));
                bid
            }
            ExprData::Return(it) => {
                match it {
                    Some(inner) => {
                        let result_slot = self.alloc_slot(Slot::Result);
                        bid = self.expr(*inner, bid, None, Some(result_slot));
                    }
                    None => {}
                }
                self.body.blocks[bid].set_terminator(Terminator::Return);
                let next_bid = target.unwrap_or_else(|| self.body.blocks.alloc(Default::default()));
                next_bid
            }
        }
    }
    fn expr_to_function(&mut self, expr: ExprIdx) -> (FunctionId, Vec<SlotId>) {
        match &self.cx.expr(expr).data {
            ExprData::Ident(var) => {
                let id = self.alloc_function(Function::new(FunctionData::Named(var.idx())));
                (id, vec![])
            }
            ExprData::Field { .. } => todo!(
                "trying to call a field: {}",
                pretty::expr(self.cx, self.db, expr)
            ),
            _ => todo!("trying to call {}", pretty::expr(self.cx, self.db, expr)),
        }
    }
    fn if_expr(
        &mut self,
        it: &IfExpr,
        mut bid: BlockId,
        target: Option<BlockId>,
        dest: Option<SlotId>,
        _expr_for_source_span: ExprIdx,
    ) -> BlockId {
        let cond = self.alloc_tmp();
        bid = self.expr(it.condition, bid, None, Some(cond));
        let then_block = self.body.blocks.alloc(Default::default());
        let else_block = self.body.blocks.alloc(Default::default());
        let final_block = target.unwrap_or_else(|| self.body.blocks.alloc(Default::default()));
        let then_block_final = self.block(&it.then_branch, then_block, Some(final_block), dest);
        let else_block_final = match it.else_branch.as_deref() {
            Some(Else::Block(it)) => self.block(it, else_block, Some(final_block), dest),
            Some(Else::If(nested)) => self.if_expr(
                nested,
                else_block,
                Some(final_block),
                dest,
                _expr_for_source_span,
            ),
            None => else_block,
        };
        if then_block_final != final_block {
            assert_ne!(then_block_final, final_block);
            self.body.blocks[then_block_final].set_terminator(Terminator::Goto(final_block));
        }
        if else_block_final != final_block {
            assert_ne!(else_block_final, final_block);
            self.body.blocks[else_block_final].set_terminator(Terminator::Goto(final_block));
        }
        self.body.blocks[bid].set_terminator(Terminator::Switch(
            cond,
            SwitchTargets::new([(1, then_block)], else_block),
        ));
        // self.alloc_instruction(
        //     Some(expr),
        //     bid,
        //     Instruction::If(cond, then_block, else_block),
        // );
        final_block
    }
}
