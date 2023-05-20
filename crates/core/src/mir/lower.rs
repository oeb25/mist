use hir::ItemSourceMap;
use mist_syntax::ast::operators::{ArithOp, BinaryOp, CmpOp};
use tracing::debug;

use crate::{
    hir::{
        self, pretty, AssertionKind, ExprData, ExprIdx, IfExpr, ItemContext, Program, Statement,
        StatementData, TypeData, TypeId, VariableIdx,
    },
    mir::{MirError, MirErrors, Operand},
};

use super::{
    BlockId, Body, BodySourceMap, BorrowKind, Function, FunctionData, FunctionId, Instruction,
    InstructionId, MExpr, Place, Projection, RangeKind, Slot, SlotId, SwitchTargets, Terminator,
};

#[salsa::tracked]
pub fn lower_program(
    db: &dyn crate::Db,
    program: Program,
) -> Vec<(hir::Item, ItemContext, ItemSourceMap, Body, BodySourceMap)> {
    let root = program.parse(db).tree();
    program.items(db).iter().filter_map(|&item_id| {
        let Some(item) = hir::item(db, &root, item_id) else { return None; };
        let Some((cx, item_source_map)) = hir::item_lower(db, program, item_id, item) else { return None; };
        let (mir, mir_source_map) = lower_item(db, cx.clone());
        Some((item, cx, item_source_map, mir, mir_source_map))
    }).collect()
}

pub fn lower_item(db: &dyn crate::Db, cx: ItemContext) -> (Body, BodySourceMap) {
    let span = cx.function_var().map(|fvar| {
        tracing::span!(
            tracing::Level::DEBUG,
            "mir::lower_item",
            "{}",
            cx.var_ident(fvar)
        )
    });
    let _enter = span.as_ref().map(|span| span.enter());

    let mut lower = MirLower::new(db, &cx);

    lower.body.params = cx
        .params()
        .iter()
        .map(|param| lower.alloc_slot(Slot::Param(param.name), cx[param.ty].ty))
        .collect();

    lower.body.result_slot = cx
        .return_ty()
        .map(|ret_ty| lower.alloc_slot(Slot::Result, ret_ty));

    lower.body.self_slot = cx
        .self_ty()
        .map(|self_ty| lower.alloc_slot(Slot::Self_, self_ty));

    for cond in cx.conditions() {
        match cond {
            hir::Condition::Requires(es) => {
                for &e in es {
                    let slot = lower.alloc_expr(e);
                    let entry_bid = lower.alloc_block(Some(e));
                    lower.expr(e, entry_bid, None, Placement::Assign(slot));
                    lower.body.requires.push(entry_bid);
                }
            }
            hir::Condition::Ensures(es) => {
                for &e in es {
                    let slot = lower.alloc_expr(e);
                    let entry_bid = lower.alloc_block(Some(e));
                    lower.expr(e, entry_bid, None, Placement::Assign(slot));
                    lower.body.ensures.push(entry_bid);
                }
            }
        }
    }

    for &ty_inv in cx.self_invariants() {
        let slot = lower.alloc_expr(ty_inv);
        let entry_bid = lower.alloc_block(Some(ty_inv));
        lower.expr(ty_inv, entry_bid, None, Placement::Assign(slot));
        lower.body.invariants.push(entry_bid);
    }

    if let Some(body) = cx.body_expr() {
        let placement = match lower.body.result_slot() {
            Some(slot) => Placement::Assign(slot.into()),
            None => Placement::Ignore,
        };
        let body_bid = lower.alloc_block(Some(body));
        lower.expr(body, body_bid, None, placement);
        lower.body.body_block = Some(body_bid);
    }

    lower.finish()
}

struct MirLower<'a> {
    db: &'a dyn crate::Db,
    cx: &'a ItemContext,

    body: Body,
    source_map: BodySourceMap,
}

impl<'a> MirLower<'a> {
    fn new(db: &'a dyn crate::Db, cx: &'a ItemContext) -> Self {
        Self {
            db,
            cx,
            body: Body::new(cx.item_id()),
            source_map: Default::default(),
        }
    }

    fn alloc_tmp(&mut self, ty: TypeId) -> Place {
        self.alloc_place(Slot::default(), ty)
    }
    fn alloc_expr(&mut self, expr: ExprIdx) -> Place {
        self.alloc_tmp(self.cx.expr_ty(expr))
    }
    fn alloc_place(&mut self, slot: Slot, ty: TypeId) -> Place {
        self.alloc_slot(slot, ty).into()
    }
    fn alloc_quantified(&mut self, var: VariableIdx) -> SlotId {
        self.alloc_slot(Slot::Quantified(var), self.cx.var_ty(var))
    }
    fn alloc_local(&mut self, var: VariableIdx) -> SlotId {
        self.alloc_slot(Slot::Local(var), self.cx.var_ty(var))
    }
    fn alloc_slot(&mut self, slot: Slot, ty: TypeId) -> SlotId {
        let id = match &slot {
            Slot::Temp => self.body.slots.alloc(slot),
            Slot::Param(var) | Slot::Local(var) | Slot::Quantified(var) => {
                let var = *var;
                let id = self.body.slots.alloc(slot);
                self.source_map.var_map.insert(var, id);
                id
            }
            Slot::Self_ => *self
                .body
                .self_slot
                .get_or_insert_with(|| self.body.slots.alloc(slot)),
            Slot::Result => *self
                .body
                .result_slot
                .get_or_insert_with(|| self.body.slots.alloc(slot)),
        };
        if let Some(old_ty) = self.body.slot_type.insert(id, ty) {
            debug!(
                "replaced a type. old was '{}' and new was '{}'",
                pretty::ty(self.cx, self.db, old_ty),
                pretty::ty(self.cx, self.db, ty)
            );
        }
        id
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
            self.source_map.expr_instr_map_back.insert(id, expr);
        }
        id
    }
    fn alloc_block(&mut self, expr: Option<ExprIdx>) -> BlockId {
        let id = self.body.blocks.alloc(Default::default());
        if let Some(expr) = expr {
            self.source_map.expr_block_map.insert(expr, id);
            self.source_map.expr_block_map_back.insert(id, expr);
        }
        id
    }
    fn hint_block_source(&mut self, source: ExprIdx, bid: BlockId) {
        if !self.source_map.expr_block_map_back.contains_idx(bid) {
            self.source_map.expr_block_map.insert(source, bid);
            self.source_map.expr_block_map_back.insert(bid, source);
        }
    }
    fn alloc_function(&mut self, function: Function) -> FunctionId {
        self.body.functions.alloc(function)
    }
    fn self_slot(&self) -> Option<SlotId> {
        self.body.self_slot
    }
    fn var_place(&mut self, var: VariableIdx) -> Place {
        if let Some(&slot) = self.source_map.var_map.get(var) {
            slot.into()
        } else {
            MirErrors::push(
                self.db,
                MirError::SlotUseBeforeAlloc {
                    item_id: self.cx.item_id(),
                    var,
                    span: Some(self.cx.var_span(var)),
                },
            );
            self.alloc_tmp(self.cx.var_ty(var))
        }
    }
    fn finish(self) -> (Body, BodySourceMap) {
        (self.body, self.source_map)
    }

    fn project_deeper(&mut self, mut place: Place, projection: &[Projection]) -> Place {
        let mut new_projection = self.body[place.projection].to_vec();
        new_projection.extend_from_slice(projection);

        if let Some((id, _)) = self
            .body
            .projections
            .iter()
            .find(|(_, proj)| proj == &&new_projection)
        {
            place.projection = id;
            return place;
        }

        place.projection = self.body.projections.alloc(new_projection);
        place
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Placement<'a> {
    Ignore,
    Assign(Place),
    IntoOperand(TypeId, &'a mut Option<Operand>),
    Assertion(AssertionKind),
    IntoPlace(TypeId, &'a mut Option<Place>),
}

impl MirLower<'_> {
    fn put(&mut self, bid: BlockId, dest: Placement, source: Option<ExprIdx>, expr: MExpr) {
        match dest {
            Placement::Ignore => {}
            Placement::Assign(slot) => {
                self.alloc_instruction(source, bid, Instruction::Assign(slot, expr));
            }
            Placement::IntoOperand(ty, u) => match &expr {
                MExpr::Use(op) => *u = Some(op.clone()),
                // TODO: Maybe something different should happen for ref
                MExpr::Ref(_, _)
                | MExpr::Struct(_, _)
                | MExpr::BinaryOp(_, _, _)
                | MExpr::UnaryOp(_, _) => {
                    let tmp = self.alloc_tmp(ty);
                    self.alloc_instruction(source, bid, Instruction::Assign(tmp, expr));
                    *u = Some(Operand::Move(tmp));
                }
            },
            Placement::IntoPlace(ty, u) => match &expr {
                MExpr::Use(op) => {
                    if let Some(place) = op.place() {
                        *u = Some(place)
                    } else {
                        let tmp = self.alloc_tmp(ty);
                        self.alloc_instruction(source, bid, Instruction::Assign(tmp, expr));
                        *u = Some(tmp);
                    }
                }
                // TODO: Maybe something different should happen for ref
                MExpr::Ref(_, _)
                | MExpr::Struct(_, _)
                | MExpr::BinaryOp(_, _, _)
                | MExpr::UnaryOp(_, _) => {
                    let tmp = self.alloc_tmp(ty);
                    self.alloc_instruction(source, bid, Instruction::Assign(tmp, expr));
                    *u = Some(tmp);
                }
            },
            Placement::Assertion(kind) => {
                self.alloc_instruction(source, bid, Instruction::Assertion(kind, expr));
            }
        }
    }

    fn put_call(
        &mut self,
        expr: ExprIdx,
        func: FunctionId,
        args: Vec<Operand>,
        dest: Placement,
        bid: BlockId,
        target: Option<BlockId>,
    ) -> BlockId {
        let (destination, next_bid, assertion) = match dest {
            Placement::Ignore => (
                self.alloc_expr(expr),
                target.unwrap_or_else(|| self.alloc_block(None)),
                None,
            ),
            Placement::Assign(slot) => {
                (slot, target.unwrap_or_else(|| self.alloc_block(None)), None)
            }
            Placement::IntoOperand(ty, into) => {
                let tmp = self.alloc_tmp(ty);
                *into = Some(Operand::Move(tmp));
                (tmp, target.unwrap_or_else(|| self.alloc_block(None)), None)
            }
            Placement::IntoPlace(ty, into) => {
                let tmp = self.alloc_tmp(ty);
                *into = Some(tmp);
                (tmp, target.unwrap_or_else(|| self.alloc_block(None)), None)
            }
            Placement::Assertion(kind) => {
                (self.alloc_expr(expr), self.alloc_block(None), Some(kind))
            }
        };

        self.body.blocks[bid].set_terminator(Terminator::Call {
            func,
            args,
            destination,
            target: Some(next_bid),
        });

        match assertion {
            Some(kind) => {
                self.alloc_instruction(
                    Some(expr),
                    next_bid,
                    Instruction::Assertion(kind, MExpr::Use(Operand::Copy(destination))),
                );
                let final_bid = target.unwrap_or_else(|| self.alloc_block(None));
                self.body.blocks[next_bid].terminator = Some(Terminator::Goto(final_bid));
                final_bid
            }
            None => next_bid,
        }
    }

    fn block(
        &mut self,
        block: &hir::Block,
        mut bid: BlockId,
        target: Option<BlockId>,
        dest: Placement,
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
            StatementData::Expr(expr) => self.expr(*expr, bid, target, Placement::Ignore),
            StatementData::Let {
                variable,
                explicit_ty: _,
                initializer,
            } => {
                let dest = self.alloc_local(variable.idx());
                self.expr(*initializer, bid, target, Placement::Assign(dest.into()))
            }
            StatementData::While {
                expr,
                invariants,
                decreases,
                body,
            } => {
                let cond_block = self.alloc_block(None);
                assert_ne!(bid, cond_block);
                self.body.blocks[bid].set_terminator(Terminator::Goto(cond_block));

                bid = cond_block;
                let cond_place = self.expr_into_place(*expr, &mut bid, None);

                let cond_inv_bid = {
                    let cond_inv_bid = self.alloc_block(None);
                    let mut end_bid = cond_inv_bid;
                    let inv_result = self.expr_into_operand(*expr, &mut end_bid, None);
                    let bool_ty = self.body.place_ty(cond_place);
                    let some_place = self.alloc_place(Slot::Temp, bool_ty);
                    self.alloc_instruction(
                        Some(*expr),
                        end_bid,
                        Instruction::Assign(
                            some_place,
                            MExpr::BinaryOp(
                                BinaryOp::CmpOp(CmpOp::Eq { negated: false }),
                                inv_result,
                                Operand::Copy(cond_place),
                            ),
                        ),
                    );
                    cond_inv_bid
                };

                let invariants: Vec<_> = invariants
                    .iter()
                    .flatten()
                    .map(|inv| {
                        let inv_block = self.alloc_block(None);
                        let inv_result = self.alloc_expr(*inv);
                        self.expr(*inv, inv_block, None, Placement::Assign(inv_result));
                        inv_block
                    })
                    .chain([cond_inv_bid])
                    .collect();

                self.body.block_invariants.insert(bid, invariants);

                let body_bid = self.alloc_block(None);
                let body_bid_last = self.block(body, body_bid, None, Placement::Ignore);

                let exit_bid = self.alloc_block(None);

                assert_ne!(body_bid_last, cond_block);
                self.body.blocks[body_bid_last].set_terminator(Terminator::Goto(cond_block));
                self.body.blocks[bid].set_terminator(Terminator::Switch(
                    Operand::Copy(cond_place),
                    SwitchTargets::new([(1, body_bid)], exit_bid),
                ));

                exit_bid
            }
            StatementData::Assertion { kind, exprs } => {
                for &expr in exprs {
                    bid = self.expr(expr, bid, None, Placement::Assertion(*kind));
                }
                bid
            }
        }
    }
    fn assign(&mut self, bid: BlockId, source: Option<ExprIdx>, dest: Place, expr: MExpr) -> Place {
        self.alloc_instruction(source, bid, Instruction::Assign(dest, expr));
        dest
    }
    fn lhs_expr(
        &mut self,
        expr: ExprIdx,
        bid: BlockId,
        _target: Option<BlockId>,
    ) -> (BlockId, Place) {
        let expr_data = self.cx.expr(expr);
        match &expr_data.data {
            ExprData::Literal(_) => todo!(),
            ExprData::Self_ => todo!(),
            ExprData::Ident(x) => (bid, self.var_place(x.idx())),
            ExprData::Block(_) => todo!(),
            ExprData::NotNull(_) => todo!(),
            ExprData::Field {
                expr: base, field, ..
            } => {
                let (bid, place) = self.lhs_expr(*base, bid, None);
                if let Some(f) = field {
                    let f_ty = expr_data.ty;
                    (
                        bid,
                        self.project_deeper(place, &[Projection::Field(f.clone(), f_ty)]),
                    )
                } else {
                    MirErrors::push(
                        self.db,
                        MirError::NotYetImplemented {
                            msg: "lhs_expr of field access".to_string(),
                            item_id: self.cx.item_id(),
                            expr,
                            span: None,
                        },
                    );

                    (bid, place)
                }
            }
            ExprData::Struct { .. } => todo!(),
            ExprData::Missing => (bid, self.alloc_tmp(self.cx.error_ty())),
            ExprData::If(_) => todo!(),
            ExprData::Call { .. } => todo!(),
            ExprData::Unary { .. } => todo!(),
            ExprData::Bin { .. } => todo!(),
            ExprData::Ref { .. } => todo!(),
            ExprData::Index { base, index } => {
                let idx = self.alloc_tmp(self.cx.expr_ty(*index));
                let bid = self.expr(*index, bid, None, Placement::Assign(idx));
                let (bid, place) = self.lhs_expr(*base, bid, None);
                (
                    bid,
                    self.project_deeper(place, &[Projection::Index(idx.slot, expr_data.ty)]),
                )
            }
            ExprData::List { .. } => todo!(),
            ExprData::Quantifier { .. } => todo!(),
            ExprData::Result => todo!(),
            ExprData::Range { .. } => todo!(),
            ExprData::Return(_) => todo!(),
        }
    }
    fn expr_into_operand(
        &mut self,
        expr: ExprIdx,
        bid: &mut BlockId,
        target: Option<BlockId>,
    ) -> Operand {
        let mut tmp = None;
        *bid = self.expr(
            expr,
            *bid,
            target,
            Placement::IntoOperand(self.cx.expr_ty(expr), &mut tmp),
        );
        tmp.unwrap_or_else(|| Operand::Move(self.alloc_expr(expr)))
    }

    fn expr_into_place(
        &mut self,
        expr: ExprIdx,
        bid: &mut BlockId,
        target: Option<BlockId>,
    ) -> Place {
        let mut tmp = None;
        *bid = self.expr(
            expr,
            *bid,
            target,
            Placement::IntoPlace(self.cx.expr_ty(expr), &mut tmp),
        );
        tmp.unwrap_or_else(|| {
            let ty = self.cx.expr_ty(expr);
            self.alloc_place(Slot::Temp, ty)
        })
    }
    fn expr(
        &mut self,
        expr: ExprIdx,
        mut bid: BlockId,
        target: Option<BlockId>,
        dest: Placement,
    ) -> BlockId {
        self.hint_block_source(expr, bid);

        let expr_data = self.cx.expr(expr);
        match &expr_data.data {
            ExprData::Literal(l) => {
                self.put(
                    bid,
                    dest,
                    Some(expr),
                    MExpr::Use(Operand::Literal(l.clone())),
                );
                bid
            }
            ExprData::Self_ => {
                if let Some(self_slot) = self.self_slot() {
                    self.put(
                        bid,
                        dest,
                        Some(expr),
                        MExpr::Use(Operand::Move(self_slot.into())),
                    );
                } else {
                    MirErrors::push(
                        self.db,
                        MirError::SelfInItemWithout {
                            item_id: self.cx.item_id(),
                            expr,
                            span: None,
                        },
                    )
                }
                bid
            }
            ExprData::Ident(var) => {
                let var_place = self.var_place(var.idx());
                self.put(bid, dest, Some(expr), MExpr::Use(Operand::Move(var_place)));
                bid
            }
            ExprData::Block(block) => {
                let next_bid = self.alloc_block(None);
                assert_ne!(bid, next_bid);
                self.body.blocks[bid].set_terminator(Terminator::Goto(next_bid));
                self.block(block, next_bid, target, dest)
            }
            ExprData::Field {
                expr: base,
                field_name: _,
                field,
            } => {
                if let Some(field) = field {
                    let tmp = self.expr_into_operand(*base, &mut bid, None);
                    if let Some(place) = tmp.place() {
                        let f_ty = expr_data.ty;
                        let field_projection =
                            self.project_deeper(place, &[Projection::Field(field.clone(), f_ty)]);
                        self.put(
                            bid,
                            dest,
                            Some(expr),
                            MExpr::Use(Operand::Move(field_projection)),
                        );
                        bid
                    } else {
                        todo!()
                    }
                } else {
                    if !self.cx.expr_ty(*base).is_error(self.cx) {
                        MirErrors::push(
                            self.db,
                            MirError::NotYetImplemented {
                                item_id: self.cx.item_id(),
                                msg: "missing field".to_string(),
                                expr,
                                span: None,
                            },
                        );
                    }
                    bid
                }
            }
            ExprData::NotNull(it) => {
                // NOTE: It the MIR level `!` is a noop
                self.expr(*it, bid, target, dest)
            }
            ExprData::Struct {
                struct_declaration,
                struct_span: _,
                fields,
            } => {
                let mut operands = vec![];

                for f in fields {
                    let tmp = self.expr_into_operand(f.value, &mut bid, None);
                    operands.push((f.decl.clone(), tmp));
                }

                self.put(
                    bid,
                    dest,
                    Some(expr),
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

                for &arg in input_args {
                    let tmp = self.expr_into_operand(arg, &mut bid, None);
                    args.push(tmp);
                }

                self.put_call(expr, func, args, dest, bid, target)
            }
            ExprData::Unary { op, inner } => {
                let tmp = self.expr_into_operand(*inner, &mut bid, None);
                self.put(bid, dest, Some(expr), MExpr::UnaryOp(*op, tmp));
                bid
            }
            &ExprData::Bin { lhs, op, rhs } => {
                match op {
                    BinaryOp::Assignment => {
                        let (mut bid, left) = self.lhs_expr(lhs, bid, None);
                        let right = self.expr_into_operand(rhs, &mut bid, None);

                        self.assign(bid, Some(expr), left, MExpr::Use(right));
                        // TODO: dest is unused? should we do anything?
                        bid
                    }
                    BinaryOp::ArithOp(ArithOp::Add)
                        if matches!(
                            self.cx.ty_data(self.cx.expr_ty(lhs).strip_ghost(self.cx)),
                            TypeData::List(_),
                        ) =>
                    {
                        let left = self.expr_into_operand(lhs, &mut bid, None);
                        let right = self.expr_into_operand(rhs, &mut bid, None);
                        let func = self.alloc_function(Function::new(FunctionData::ListConcat));
                        self.put_call(expr, func, vec![left, right], dest, bid, target)
                    }
                    _ => {
                        let left = self.expr_into_operand(lhs, &mut bid, None);
                        let right = self.expr_into_operand(rhs, &mut bid, None);
                        self.put(bid, dest, Some(expr), MExpr::BinaryOp(op, left, right));
                        bid
                    }
                }
            }
            ExprData::Ref {
                is_mut,
                expr: inner,
            } => {
                let bk = if *is_mut {
                    BorrowKind::Mutable
                } else {
                    BorrowKind::Shared
                };
                let p = self.expr_into_place(*inner, &mut bid, None);
                self.put(bid, dest, Some(expr), MExpr::Ref(bk, p));
                bid
            }
            &ExprData::Index { base, index } => {
                let f = match self.cx.ty_data_without_ghost(self.cx.expr_ty(index)) {
                    hir::TypeData::Range(_) => FunctionData::RangeIndex,
                    hir::TypeData::Primitive(hir::Primitive::Int) => FunctionData::Index,
                    hir::TypeData::Error => FunctionData::Index,
                    ty => todo!("tried to index with {ty:?}"),
                };
                let base_s = self.expr_into_operand(base, &mut bid, None);
                let index_s = self.expr_into_operand(index, &mut bid, None);
                let func = self.alloc_function(Function::new(f));

                self.put_call(expr, func, vec![base_s, index_s], dest, bid, target)
            }
            ExprData::List { elems } => {
                let elems = elems
                    .iter()
                    .map(|&e| self.expr_into_operand(e, &mut bid, None))
                    .collect();
                let func = self.alloc_function(Function::new(FunctionData::List));

                self.put_call(expr, func, elems, dest, bid, target)
            }
            ExprData::Quantifier {
                quantifier,
                params,
                expr: q_expr,
            } => {
                let q_body = self.alloc_block(None);
                let params = params
                    .iter()
                    .map(|param| self.alloc_quantified(param.name))
                    .collect();

                let mut q_end = q_body;
                let q_dest = self.expr_into_operand(*q_expr, &mut q_end, None);
                let next_bid = target.unwrap_or_else(|| self.alloc_block(None));
                assert_ne!(bid, next_bid);

                self.body.blocks[bid].set_terminator(Terminator::Quantify(
                    *quantifier,
                    params,
                    q_body,
                ));
                self.body.blocks[q_end].set_terminator(Terminator::QuantifyEnd(next_bid));

                next_bid
            }
            ExprData::Result => {
                if let Some(result_slot) = self.body.result_slot() {
                    self.put(
                        bid,
                        dest,
                        Some(expr),
                        MExpr::Use(Operand::Move(result_slot.into())),
                    );
                } else {
                    MirErrors::push(
                        self.db,
                        MirError::ResultWithoutReturnSlot {
                            item_id: self.cx.item_id(),
                            expr,
                            span: None,
                        },
                    );
                    todo!();
                    // self.alloc_slot(Slot::Result, expr_ty)
                };
                bid
            }
            ExprData::Range { lhs, rhs } => {
                let kind = match (lhs, rhs) {
                    (None, None) => RangeKind::Full,
                    (None, Some(_)) => RangeKind::To,
                    (Some(_), None) => RangeKind::From,
                    (Some(_), Some(_)) => RangeKind::FromTo,
                };
                let func = self.alloc_function(Function::new(FunctionData::Range(kind)));

                let args = [lhs, rhs]
                    .into_iter()
                    .flatten()
                    .map(|&a| self.expr_into_operand(a, &mut bid, None))
                    .collect();

                self.put_call(expr, func, args, dest, bid, target)
            }
            ExprData::Return(it) => {
                match it {
                    Some(inner) => {
                        let result_slot = if let Some(result_slot) = self.body.result_slot() {
                            result_slot
                        } else {
                            MirErrors::push(
                                self.db,
                                MirError::ResultWithoutReturnSlot {
                                    item_id: self.cx.item_id(),
                                    expr,
                                    span: None,
                                },
                            );
                            todo!()
                            // self.alloc_slot(Slot::Result, expr_ty)
                        };
                        let result_operand = self.expr_into_operand(*inner, &mut bid, None);
                        self.assign(
                            bid,
                            Some(expr),
                            result_slot.into(),
                            MExpr::Use(result_operand),
                        );
                        // TODO: dest is unused?
                    }
                    None => {}
                }
                self.body.blocks[bid].set_terminator(Terminator::Return);
                target.unwrap_or_else(|| self.alloc_block(None))
            }
        }
    }
    fn expr_to_function(&mut self, expr: ExprIdx) -> (FunctionId, Vec<Operand>) {
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
        dest: Placement,
        _expr_for_source_span: ExprIdx,
    ) -> BlockId {
        let cond = self.expr_into_operand(it.condition, &mut bid, None);
        let then_block = self.alloc_block(Some(it.then_branch));
        let else_block = self.alloc_block(it.else_branch);
        let final_block = target.unwrap_or_else(|| self.alloc_block(None));

        let (then_dest, else_dest) = match dest {
            Placement::Ignore => (Placement::Ignore, Placement::Ignore),
            Placement::Assign(p) => (Placement::Assign(p), Placement::Assign(p)),
            Placement::IntoOperand(ty, o) => {
                let tmp = self.alloc_tmp(ty);
                *o = Some(Operand::Move(tmp));
                (Placement::Assign(tmp), Placement::Assign(tmp))
            }
            Placement::IntoPlace(ty, o) => {
                let tmp = self.alloc_tmp(ty);
                *o = Some(tmp);
                (Placement::Assign(tmp), Placement::Assign(tmp))
            }
            Placement::Assertion(kind) => (Placement::Assertion(kind), Placement::Assertion(kind)),
        };

        let then_block_final = self.expr(it.then_branch, then_block, Some(final_block), then_dest);
        let else_block_final = match it.else_branch {
            Some(else_exp) => self.expr(else_exp, else_block, Some(final_block), else_dest),
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
        final_block
    }
}
