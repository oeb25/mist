use itertools::Itertools;
use mist_syntax::ast::operators::{ArithOp, BinaryOp, CmpOp};
use tracing::debug;

use crate::{
    def::Def,
    hir::{
        self, pretty, AssertionKind, ExprData, ExprIdx, IfExpr, ItemContext, Let, StatementData,
        StatementId, VariableIdx,
    },
    mir::{MirError, MirErrors, Operand},
    types::{
        builtin::{bool, error, int},
        Field, ListField, Primitive, TypeDataKind as TDK, TypeId,
    },
};

use super::{
    BlockId, Body, BodySourceMap, BorrowKind, DefinitionMir, Function, FunctionData, FunctionId,
    Instruction, InstructionId, MExpr, Place, Projection, RangeKind, Slot, SlotId, SwitchTargets,
    Terminator,
};

#[salsa::tracked]
pub fn lower_item(db: &dyn crate::Db, def: Def) -> Option<DefinitionMir> {
    let cx = def.hir(db)?.cx(db);
    let span = cx.function_var().map(|fvar| {
        tracing::span!(tracing::Level::DEBUG, "mir::lower_item", "{}", cx.var_name(fvar))
    });
    let _enter = span.as_ref().map(|span| span.enter());

    let mut lower = MirLower::new(db, cx);

    lower.body.params = cx
        .params()
        .iter()
        .map(|param| lower.alloc_slot(Slot::Param(param.name), param.ty.ty(db)))
        .collect();

    lower.body.result_slot = cx.return_ty(db).map(|ret_ty| lower.alloc_slot(Slot::Result, ret_ty));

    lower.body.self_slot = cx.self_ty(db).map(|self_ty| lower.alloc_slot(Slot::Self_, self_ty));

    for cond in cx.conditions() {
        match cond {
            hir::Condition::Requires(es) => {
                for &e in es {
                    let slot = lower.alloc_place_for_expr(e);
                    let entry_bid = lower.alloc_block(Some(e));
                    lower.expr(e, entry_bid, None, Placement::Assign(slot));
                    lower.body.requires.push(entry_bid);
                }
            }
            hir::Condition::Ensures(es) => {
                for &e in es {
                    let slot = lower.alloc_place_for_expr(e);
                    let entry_bid = lower.alloc_block(Some(e));
                    lower.expr(e, entry_bid, None, Placement::Assign(slot));
                    lower.body.ensures.push(entry_bid);
                }
            }
        }
    }

    for &ty_inv in cx.self_invariants() {
        let slot = lower.alloc_place_for_expr(ty_inv);
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

    Some(lower.finish())
}

struct MirLower<'a> {
    db: &'a dyn crate::Db,
    cx: &'a ItemContext,

    body: Body,
    source_map: BodySourceMap,
}

impl<'a> MirLower<'a> {
    fn new(db: &'a dyn crate::Db, cx: &'a ItemContext) -> Self {
        Self { db, cx, body: Body::new(cx.def(), cx.ty_table()), source_map: Default::default() }
    }

    fn alloc_tmp(&mut self, ty: impl Into<TypeId>) -> Place {
        self.alloc_place(Slot::default(), ty)
    }
    fn alloc_place_for_expr(&mut self, expr: ExprIdx) -> Place {
        self.alloc_tmp(self.cx.expr_ty(expr))
    }
    fn alloc_place(&mut self, slot: Slot, ty: impl Into<TypeId>) -> Place {
        self.alloc_slot(slot, ty).into()
    }
    fn alloc_quantified(&mut self, var: VariableIdx) -> SlotId {
        self.alloc_slot(Slot::Quantified(var), self.cx.var_ty(self.db, var))
    }
    fn alloc_local(&mut self, var: VariableIdx) -> SlotId {
        self.alloc_slot(Slot::Local(var), self.cx.var_ty(self.db, var))
    }
    fn alloc_slot(&mut self, slot: Slot, ty: impl Into<TypeId>) -> SlotId {
        let id = match &slot {
            Slot::Temp => self.body.slots.alloc(slot),
            Slot::Param(var) | Slot::Local(var) | Slot::Quantified(var) => {
                let var = *var;
                let id = self.body.slots.alloc(slot);
                self.source_map.var_map.insert(var, id);
                id
            }
            Slot::Self_ => *self.body.self_slot.get_or_insert_with(|| self.body.slots.alloc(slot)),
            Slot::Result => {
                *self.body.result_slot.get_or_insert_with(|| self.body.slots.alloc(slot))
            }
        };
        let ty = ty.into();
        if let Some(old_ty) = self.body.slot_type.insert(id, ty) {
            debug!(
                "replaced a type. old was '{}' and new was '{}'",
                pretty::ty(self.cx, self.db, false, old_ty),
                pretty::ty(self.cx, self.db, false, ty)
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
            self.source_map.expr_instr_map.entry(expr).or_default().push(id);
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
                MirError::SlotUseBeforeAlloc { def: self.cx.def(), var, span: None },
            );
            self.alloc_tmp(self.cx.var_ty(self.db, var))
        }
    }
    fn finish(self) -> DefinitionMir {
        DefinitionMir::new(self.db, self.body, self.source_map)
    }

    fn project_deeper(&mut self, mut place: Place, projection: &[Projection]) -> Place {
        let mut new_projection = self.body[place.projection].to_vec();
        new_projection.extend_from_slice(projection);

        if let Some((id, _)) =
            self.body.projections.iter().find(|(_, proj)| proj == &&new_projection)
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
                MExpr::Ref(_, _) | MExpr::BinaryOp(_, _, _) | MExpr::UnaryOp(_, _) => {
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
                MExpr::Ref(_, _) | MExpr::BinaryOp(_, _, _) | MExpr::UnaryOp(_, _) => {
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
                self.alloc_place_for_expr(expr),
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
                (self.alloc_place_for_expr(expr), self.alloc_block(None), Some(kind))
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
        for &stmt in &block.stmts {
            bid = self.stmt(bid, None, stmt);
        }
        if let Some(tail) = block.tail_expr {
            self.expr(tail, bid, target, dest)
        } else {
            bid
        }
    }
    fn stmt(&mut self, mut bid: BlockId, target: Option<BlockId>, stmt: StatementId) -> BlockId {
        match &self.cx[stmt].data {
            StatementData::Expr(expr) => self.expr(*expr, bid, target, Placement::Ignore),
            StatementData::Let(Let { variable, initializer }) => {
                let dest = self.alloc_local(*variable);
                self.expr(*initializer, bid, target, Placement::Assign(dest.into()))
            }
            StatementData::Assertion { kind, exprs } => {
                for &expr in exprs {
                    bid = self.expr(expr, bid, None, Placement::Assertion(*kind));
                }
                bid
            }
        }
    }

    fn emit_decreases_assertion(
        &mut self,
        initial_variant: Place,
        variant: ExprIdx,
        bid: &mut BlockId,
    ) {
        let last_variant_operand = self.expr_into_operand(variant, bid, None);

        let mut assertions = vec![];

        let a = || last_variant_operand.clone();
        let b = || Operand::Move(initial_variant);

        let variant_ty = self.cx.expr_ty(variant);
        match variant_ty.kind() {
            TDK::Error => {}
            TDK::Void => {}
            TDK::Ref { .. } => todo!(),
            // a <_ b <==> |a| < |b|
            TDK::List(_) => {
                let mut len = |o| match o {
                    Operand::Copy(p) | Operand::Move(p) => self.project_deeper(
                        p,
                        &[Projection::Field(Field::List(variant_ty.id(), ListField::Len), int())],
                    ),
                    Operand::Literal(_) => todo!(),
                };

                assertions.push(MExpr::BinaryOp(
                    BinaryOp::lt(),
                    Operand::Copy(len(a())),
                    Operand::Copy(len(b())),
                ));
            }
            // a <_ b <==> a == null && b != null
            TDK::Optional(_) => {
                assertions.push(MExpr::BinaryOp(
                    BinaryOp::eq(),
                    a(),
                    Operand::Literal(hir::Literal::Null),
                ));
                assertions.push(MExpr::BinaryOp(
                    BinaryOp::ne(),
                    b(),
                    Operand::Literal(hir::Literal::Null),
                ));
            }
            // a <_ b <==> a < b && 0 <= b
            TDK::Primitive(Primitive::Int) => {
                assertions.push(MExpr::BinaryOp(BinaryOp::lt(), a(), b()));
                assertions.push(MExpr::BinaryOp(
                    BinaryOp::le(),
                    Operand::Literal(hir::Literal::Int(0)),
                    b(),
                ));
            }
            // a <_ b <==> a == false && b == true
            TDK::Primitive(Primitive::Bool) => {
                assertions.push(MExpr::BinaryOp(
                    BinaryOp::eq(),
                    a(),
                    Operand::Literal(hir::Literal::Bool(false)),
                ));
                assertions.push(MExpr::BinaryOp(
                    BinaryOp::eq(),
                    b(),
                    Operand::Literal(hir::Literal::Bool(true)),
                ));
            }
            TDK::Struct(_) => todo!(),
            TDK::Function { .. } => todo!(),
            TDK::Range(_) => todo!(),
            TDK::Null | TDK::Free => {
                assertions.push(MExpr::Use(Operand::Literal(hir::Literal::Bool(false))))
            }
        }

        for assertion in assertions {
            self.alloc_instruction(
                Some(variant),
                *bid,
                Instruction::Assertion(AssertionKind::Assert, assertion),
            );
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
            ExprData::Ident(x) => (bid, self.var_place(*x)),
            ExprData::Block(_) => todo!(),
            ExprData::NotNull(_) => todo!(),
            ExprData::Field { expr: base, field, .. } => {
                let (bid, place) = self.lhs_expr(*base, bid, None);
                match field {
                    Field::StructField(_) | Field::List(_, _) => {
                        let f_ty = expr_data.ty;
                        (bid, self.project_deeper(place, &[Projection::Field(*field, f_ty)]))
                    }
                    Field::Undefined => {
                        MirErrors::push(
                            self.db,
                            MirError::NotYetImplemented {
                                msg: "lhs_expr of field access".to_string(),
                                def: self.cx.def(),
                                expr,
                                span: None,
                            },
                        );

                        (bid, place)
                    }
                }
            }
            ExprData::Struct { .. } => todo!(),
            ExprData::Missing => (bid, self.alloc_tmp(error())),
            ExprData::If(_) => todo!(),
            ExprData::For { .. } => todo!(),
            ExprData::While { .. } => todo!(),
            ExprData::Call { .. } => todo!(),
            ExprData::Unary { .. } => todo!(),
            ExprData::Bin { .. } => todo!(),
            ExprData::Ref { .. } => todo!(),
            ExprData::Index { base, index } => {
                let idx = self.alloc_tmp(self.cx.expr_ty(*index));
                let bid = self.expr(*index, bid, None, Placement::Assign(idx));
                let (bid, place) = self.lhs_expr(*base, bid, None);
                (bid, self.project_deeper(place, &[Projection::Index(idx.slot, expr_data.ty)]))
            }
            ExprData::List { .. } => todo!(),
            ExprData::Quantifier { .. } => todo!(),
            ExprData::Result => todo!(),
            ExprData::Range { .. } => todo!(),
            ExprData::Return(_) => todo!(),
            ExprData::Builtin(_) => todo!(),
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
            Placement::IntoOperand(self.cx.expr_ty(expr).id(), &mut tmp),
        );
        tmp.unwrap_or_else(|| Operand::Move(self.alloc_place_for_expr(expr)))
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
            Placement::IntoPlace(self.cx.expr_ty(expr).id(), &mut tmp),
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
                self.put(bid, dest, Some(expr), MExpr::Use(Operand::Literal(l.clone())));
                bid
            }
            ExprData::Self_ => {
                if let Some(self_slot) = self.self_slot() {
                    self.put(bid, dest, Some(expr), MExpr::Use(Operand::Move(self_slot.into())));
                } else {
                    MirErrors::push(
                        self.db,
                        MirError::SelfInItemWithout { def: self.cx.def(), expr, span: None },
                    )
                }
                bid
            }
            ExprData::Ident(var) => {
                let var_place = self.var_place(*var);
                self.put(bid, dest, Some(expr), MExpr::Use(Operand::Move(var_place)));
                bid
            }
            ExprData::Block(block) => {
                let next_bid = self.alloc_block(None);
                assert_ne!(bid, next_bid);
                self.body.blocks[bid].set_terminator(Terminator::Goto(next_bid));
                self.block(block, next_bid, target, dest)
            }
            ExprData::Field { expr: base, field_name: _, field } => match field {
                Field::StructField(_) | Field::List(_, _) => {
                    let tmp = self.expr_into_operand(*base, &mut bid, None);
                    if let Some(place) = tmp.place() {
                        let f_ty = expr_data.ty;
                        let field_projection =
                            self.project_deeper(place, &[Projection::Field(*field, f_ty)]);
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
                }
                Field::Undefined => {
                    if !self.cx.expr_ty(*base).data().is_error() {
                        MirErrors::push(
                            self.db,
                            MirError::NotYetImplemented {
                                def: self.cx.def(),
                                msg: "missing field".to_string(),
                                expr,
                                span: None,
                            },
                        );
                    }
                    bid
                }
            },
            ExprData::NotNull(it) => {
                // NOTE: It the MIR level `!` is a noop
                self.expr(*it, bid, target, dest)
            }
            ExprData::Struct { struct_declaration, fields } => {
                let mut operands = vec![];

                for f in fields {
                    let tmp = self.expr_into_operand(f.value, &mut bid, None);
                    operands.push((f.decl, tmp));
                }

                let dest = match dest {
                    Placement::Ignore => {
                        self.alloc_tmp(self.cx.struct_ty(self.db, *struct_declaration))
                    }
                    Placement::Assign(p) => p,
                    Placement::IntoOperand(ty, o) => {
                        let tmp = self.alloc_tmp(ty);
                        *o = Some(Operand::Move(tmp));
                        tmp
                    }
                    Placement::IntoPlace(ty, o) => {
                        let tmp = self.alloc_tmp(ty);
                        *o = Some(tmp);
                        tmp
                    }
                    Placement::Assertion(_) => {
                        todo!("mir lowering of assertion where the expr is a struct")
                    }
                };

                let inst = Instruction::NewStruct(dest, *struct_declaration, operands);
                self.alloc_instruction(Some(expr), bid, inst);

                bid
            }
            ExprData::Missing => bid,
            ExprData::If(it) => self.if_expr(it, bid, target, dest, expr),
            ExprData::While(it) => self.while_expr(it, bid),
            ExprData::For(it) => self.for_expr(it, bid, expr),
            ExprData::Call { expr: f_expr, args: input_args } => {
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
                        if matches!(self.cx.expr_ty(lhs).kind(), TDK::List(_),) =>
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
            ExprData::Ref { is_mut, expr: inner } => {
                let bk = if *is_mut { BorrowKind::Mutable } else { BorrowKind::Shared };
                let p = self.expr_into_place(*inner, &mut bid, None);
                self.put(bid, dest, Some(expr), MExpr::Ref(bk, p));
                bid
            }
            &ExprData::Index { base, index } => {
                let f = match self.cx.expr_ty(index).kind() {
                    TDK::Range(_) => FunctionData::RangeIndex,
                    TDK::Primitive(Primitive::Int) => FunctionData::Index,
                    TDK::Error => FunctionData::Index,
                    ty => todo!("tried to index with {ty:?}"),
                };
                let base_s = self.expr_into_operand(base, &mut bid, None);
                let index_s = self.expr_into_operand(index, &mut bid, None);
                let func = self.alloc_function(Function::new(f));

                self.put_call(expr, func, vec![base_s, index_s], dest, bid, target)
            }
            ExprData::List { elems } => {
                let elems =
                    elems.iter().map(|&e| self.expr_into_operand(e, &mut bid, None)).collect();
                let func = self.alloc_function(Function::new(FunctionData::List));

                self.put_call(expr, func, elems, dest, bid, target)
            }
            ExprData::Quantifier { quantifier, over, expr: q_expr } => {
                let vars = match over {
                    hir::QuantifierOver::Vars(vars) => vars,
                    hir::QuantifierOver::In(_, _) => {
                        unreachable!("we should desugar quantifier-in in hir")
                    }
                };

                let q_body = self.alloc_block(None);
                let vars = vars.iter().map(|var| self.alloc_quantified(*var)).collect();

                let mut q_end = q_body;
                let q_dest = self.expr_into_operand(*q_expr, &mut q_end, None);
                let next_bid = target.unwrap_or_else(|| self.alloc_block(None));
                assert_ne!(bid, next_bid);

                self.body.blocks[bid].set_terminator(Terminator::Quantify(
                    *quantifier,
                    vars,
                    q_body,
                ));
                self.body.blocks[q_end].set_terminator(Terminator::QuantifyEnd(next_bid));

                next_bid
            }
            ExprData::Result => {
                if let Some(result_slot) = self.body.result_slot() {
                    self.put(bid, dest, Some(expr), MExpr::Use(Operand::Move(result_slot.into())));
                } else {
                    MirErrors::push(
                        self.db,
                        MirError::ResultWithoutReturnSlot { def: self.cx.def(), expr, span: None },
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
                                    def: self.cx.def(),
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
            ExprData::Builtin(b) => match b {
                hir::BuiltinExpr::RangeMin(r) => {
                    let r = self.expr_into_operand(*r, &mut bid, None);
                    let func = self.alloc_function(Function::new(FunctionData::RangeMin));
                    self.put_call(expr, func, vec![r], dest, bid, target)
                }
                hir::BuiltinExpr::RangeMax(r) => {
                    let r = self.expr_into_operand(*r, &mut bid, None);
                    let func = self.alloc_function(Function::new(FunctionData::RangeMax));
                    self.put_call(expr, func, vec![r], dest, bid, target)
                }
                hir::BuiltinExpr::InRange(idx, r) => {
                    let idx = self.expr_into_operand(*idx, &mut bid, None);
                    let r = self.expr_into_operand(*r, &mut bid, None);
                    let func = self.alloc_function(Function::new(FunctionData::InRange));
                    self.put_call(expr, func, vec![idx, r], dest, bid, target)
                }
            },
        }
    }
    fn expr_to_function(&mut self, expr: ExprIdx) -> (FunctionId, Vec<Operand>) {
        match &self.cx.expr(expr).data {
            ExprData::Ident(var) => {
                let id = self.alloc_function(Function::new(FunctionData::Named(*var)));
                (id, vec![])
            }
            ExprData::Field { .. } => {
                todo!("trying to call a field: {}", pretty::expr(self.cx, self.db, expr))
            }
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

    // TODO: perhaps remove this, since for-loops should be desugared into while loops
    fn for_expr(&mut self, _it: &hir::ForExpr, bid: BlockId, _expr: ExprIdx) -> BlockId {
        bid
    }

    fn while_expr(&mut self, it: &hir::WhileExpr, mut bid: BlockId) -> BlockId {
        let cond_block = self.alloc_block(None);
        assert_ne!(bid, cond_block);
        self.body.blocks[bid].set_terminator(Terminator::Goto(cond_block));
        bid = cond_block;
        let cond_place = self.alloc_tmp(bool());
        bid = self.expr(it.expr, bid, None, Placement::Assign(cond_place));
        let cond_inv_bid = {
            let cond_inv_bid = self.alloc_block(None);
            let mut end_bid = cond_inv_bid;
            let inv_result = self.expr_into_operand(it.expr, &mut end_bid, None);
            let some_place = self.alloc_place(Slot::Temp, bool());
            self.alloc_instruction(
                Some(it.expr),
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
        let invariants = it
            .invariants
            .iter()
            .flatten()
            .map(|inv| {
                let inv_block = self.alloc_block(None);
                let inv_result = self.alloc_place_for_expr(*inv);
                self.expr(*inv, inv_block, None, Placement::Assign(inv_result));
                inv_block
            })
            .chain([cond_inv_bid])
            .collect_vec();
        let cond_bid_last = bid;
        self.body.block_invariants.insert(cond_bid_last, invariants);
        let body_bid = self.alloc_block(None);
        let mut next_bid = body_bid;
        let variant_slot = match it.decreases {
            hir::Decreases::Unspecified => None,
            hir::Decreases::Expr(variant) => {
                let variant_slot = self.alloc_tmp(self.cx.expr_ty(variant));
                next_bid = self.expr(variant, next_bid, None, Placement::Assign(variant_slot));
                Some(variant_slot)
            }
            hir::Decreases::Inferred => None,
        };
        let mut body_bid_last = self.expr(it.body, next_bid, None, Placement::Ignore);
        if let (hir::Decreases::Expr(variant), Some(variant_slot)) = (it.decreases, variant_slot) {
            self.emit_decreases_assertion(variant_slot, variant, &mut body_bid_last);
        }
        let exit_bid = self.alloc_block(None);
        assert_ne!(body_bid_last, cond_block);
        self.body.blocks[body_bid_last].set_terminator(Terminator::Goto(cond_block));
        self.body.blocks[cond_bid_last].set_terminator(Terminator::Switch(
            Operand::Copy(cond_place),
            SwitchTargets::new([(1, body_bid)], exit_bid),
        ));
        exit_bid
    }
}
