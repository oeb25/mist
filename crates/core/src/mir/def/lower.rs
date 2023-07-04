use itertools::Itertools;
use mist_syntax::ast::operators::{ArithOp, BinaryOp, CmpOp};
use tracing::debug;

use crate::{
    hir::{self, AssertionKind},
    mir::{BodySourceMap, ItemMir, MirError, MirErrors, Operand, Projection, Slot},
    mono::{
        exprs::{
            Block as MonoBlock, BuiltinExpr, Decreases, ExprData, ExprFunction, ExprPtr, Field,
            ForExpr, IfExpr, Let, QuantifierOver, Statement, StatementData, VariablePtr, WhileExpr,
        },
        types::{Type, TypeData},
        Condition, Item, ItemKind,
    },
    types::{BuiltinField, BuiltinKind, ListField, Primitive},
    util::{SourceMapped, SourceMappedMulti},
};

use super::{
    BlockId, Body, BorrowKind, Function, Instruction, InstructionId, ItemBody, MExpr, Place,
    RangeKind, SlotId, SwitchTargets, Terminator, TerminatorKind,
};

#[salsa::tracked]
pub fn lower_item(db: &dyn crate::Db, item: Item) -> Option<ItemMir> {
    lower_item_internal(db, item)
}
fn lower_item_internal(db: &dyn crate::Db, item: Item) -> Option<ItemMir> {
    let span = tracing::span!(tracing::Level::DEBUG, "mir::lower_item", "{}", item.name(db));
    let _enter = span.enter();

    let mut lower = MirLower::new(db, item);
    let mut params = Vec::new();
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    let mut invariants = Vec::new();
    let mut body_block = None;

    match item.kind(db) {
        ItemKind::Adt(adt) => {
            for ty_inv in adt.invariants(db) {
                let slot = lower.alloc_place_for_expr(ty_inv);
                let entry_bid = lower.alloc_block(Some(ty_inv));
                lower.expr(ty_inv, entry_bid, None, Placement::Assign(slot));
                invariants.push(entry_bid);
            }
        }
        ItemKind::Function(fun) => {
            params = fun
                .params(db)
                .iter()
                .map(|param| lower.alloc_slot(Slot::Param(param.name), param.ty))
                .collect();

            for cond in fun.conditions(db) {
                match cond {
                    Condition::Requires(es) => {
                        for e in es {
                            let slot = lower.alloc_place_for_expr(e);
                            let entry_bid = lower.alloc_block(Some(e));
                            lower.expr(e, entry_bid, None, Placement::Assign(slot));
                            requires.push(entry_bid);
                        }
                    }
                    Condition::Ensures(es) => {
                        for e in es {
                            let slot = lower.alloc_place_for_expr(e);
                            let entry_bid = lower.alloc_block(Some(e));
                            lower.expr(e, entry_bid, None, Placement::Assign(slot));
                            ensures.push(entry_bid);
                        }
                    }
                }
            }

            if let Some(body) = fun.body(db) {
                let placement = match lower.body.result_slot {
                    Some(slot) => Placement::Assign(slot.place(db, &lower.body)),
                    None => Placement::Ignore,
                };
                let body_bid = lower.alloc_block(Some(body));
                lower.expr(body, body_bid, None, placement);
                body_block = Some(body_bid);
            }
        }
    }

    let (body, source_map) = lower.finish();
    let ib = ItemBody { item, body, params, requires, ensures, invariants, body_block };
    Some(ItemMir::new(db, ib, source_map))
}

struct MirLower<'a> {
    db: &'a dyn crate::Db,
    body: Body,
    source_map: BodySourceMap,
}

impl<'a> MirLower<'a> {
    fn new(db: &'a dyn crate::Db, item: Item) -> Self {
        let mut l = Self { db, body: Body::new(item), source_map: Default::default() };

        let self_ty = match item.kind(db) {
            ItemKind::Adt(adt) => Some(adt.ty(db)),
            ItemKind::Function(_) => None,
        };
        l.body.self_slot = self_ty.map(|ty| l.alloc_slot(Slot::Self_, ty));

        let result_ty = match item.kind(db) {
            ItemKind::Adt(_) => None,
            ItemKind::Function(f) => Some(f.return_ty(db)),
        };
        l.body.result_slot = result_ty.map(|ty| l.alloc_slot(Slot::Result, ty));

        l
    }

    fn alloc_tmp(&mut self, ty: Type) -> Place {
        self.alloc_place(Slot::default(), ty)
    }
    fn alloc_place_for_expr(&mut self, expr: ExprPtr) -> Place {
        self.alloc_tmp(expr.ty())
    }
    fn alloc_place(&mut self, slot: Slot, ty: Type) -> Place {
        let s = self.alloc_slot(slot, ty);
        self.place(s)
    }
    fn alloc_quantified(&mut self, var: VariablePtr) -> SlotId {
        self.alloc_slot(Slot::Quantified(var), var.ty())
    }
    fn alloc_local(&mut self, var: VariablePtr) -> SlotId {
        self.alloc_slot(Slot::Local(var), var.ty())
    }
    fn alloc_slot(&mut self, slot: Slot, ty: Type) -> SlotId {
        let id = match &slot {
            Slot::Temp => self.body.slots.alloc(slot),
            Slot::Param(var) | Slot::Local(var) | Slot::Quantified(var) => {
                let var = *var;
                let id = self.body.slots.alloc(slot);
                self.source_map.register(var, id);
                id
            }
            Slot::Self_ => {
                assert_eq!(self.body.self_slot, None);
                let id = self.body.slots.alloc(Slot::Self_);
                self.body.self_slot = Some(id);
                id
            }
            Slot::Result => {
                assert_eq!(self.body.result_slot, None);
                let id = self.body.slots.alloc(Slot::Result);
                self.body.result_slot = Some(id);
                id
            }
        };
        if let Some(old_ty) = self.body.slot_type.insert(id, ty) {
            debug!(
                "replaced a type. old was '{}' and new was '{}'",
                old_ty.display(self.db),
                ty.display(self.db),
            );
        }
        id
    }
    fn alloc_instruction(
        &mut self,
        expr: Option<ExprPtr>,
        bid: BlockId,
        instruction: Instruction,
    ) -> InstructionId {
        let id = self.body.instructions.alloc(instruction);
        self.body.blocks[bid].instructions.push(id);
        if let Some(expr) = expr {
            self.source_map.register_multi(expr, id);
        }
        id
    }
    fn alloc_block(&mut self, expr: Option<ExprPtr>) -> BlockId {
        let id = self.body.blocks.alloc(Default::default());
        if let Some(expr) = expr {
            self.source_map.register(expr, id);
        }
        id
    }
    fn set_block_invariants(&mut self, bid: BlockId, invariants: Vec<BlockId>) {
        self.body.block_invariants.insert(bid, invariants);
    }
    fn hint_block_source(&mut self, source: ExprPtr, bid: BlockId) {
        if !self.source_map.has_back(bid) {
            self.source_map.register(source, bid);
        }
    }
    fn self_slot(&self) -> Option<SlotId> {
        self.body.self_slot
    }
    fn var_place(&mut self, var: VariablePtr) -> Place {
        if let Some(slot) = self.source_map.find(var) {
            slot.place(self.db, &self.body)
        } else {
            MirErrors::push(self.db, MirError::SlotUseBeforeAlloc { var, span: None });
            self.alloc_tmp(var.ty())
        }
    }
    fn finish(self) -> (Body, BodySourceMap) {
        (self.body, self.source_map)
    }

    fn set_terminator(&mut self, bid: BlockId, term: Terminator) -> Option<Terminator> {
        let old = self.body.blocks[bid].terminator.replace(term);
        if let Some(_old) = &old {
            debug!("terminator was replaced!");
        }
        old
    }

    fn place(&self, s: SlotId) -> Place {
        s.place(self.db, &self.body)
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Placement<'a> {
    Ignore,
    Assign(Place),
    IntoOperand(Type, &'a mut Option<Operand>),
    Assertion(AssertionKind),
    IntoPlace(Type, &'a mut Option<Place>),
}

impl MirLower<'_> {
    fn put(&mut self, bid: BlockId, dest: Placement, source: Option<ExprPtr>, expr: MExpr) {
        match dest {
            Placement::Ignore => {}
            Placement::Assign(slot) => {
                self.alloc_instruction(source, bid, Instruction::Assign(slot, expr));
            }
            Placement::IntoOperand(ty, u) => match &expr {
                MExpr::Use(op) => *u = Some(*op),
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
        expr: ExprPtr,
        func: Function,
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

        let term = Terminator::new(
            self.db,
            TerminatorKind::Call { func, args, destination, target: Some(next_bid) },
        );
        self.set_terminator(bid, term);

        match assertion {
            Some(kind) => {
                self.alloc_instruction(
                    Some(expr),
                    next_bid,
                    Instruction::Assertion(kind, MExpr::Use(Operand::Copy(destination))),
                );
                let final_bid = target.unwrap_or_else(|| self.alloc_block(None));
                let goto = Terminator::goto(self.db, final_bid);
                self.set_terminator(next_bid, goto);
                final_bid
            }
            None => next_bid,
        }
    }

    fn block(
        &mut self,
        block: &MonoBlock,
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
    fn stmt(&mut self, mut bid: BlockId, target: Option<BlockId>, stmt: Statement) -> BlockId {
        match stmt.data(self.db) {
            StatementData::Expr(expr) => self.expr(expr, bid, target, Placement::Ignore),
            StatementData::Let(Let { variable, initializer }) => {
                let dest = if let Some(var) = variable {
                    self.alloc_local(var)
                } else {
                    self.alloc_tmp(initializer.ty()).slot()
                };
                self.expr(initializer, bid, target, Placement::Assign(self.place(dest)))
            }
            StatementData::Assertion { kind, exprs } => {
                for expr in exprs {
                    bid = self.expr(expr, bid, None, Placement::Assertion(kind));
                }
                bid
            }
        }
    }

    fn emit_decreases_assertion(
        &mut self,
        initial_variant: Place,
        variant: ExprPtr,
        bid: &mut BlockId,
    ) {
        let last_variant_operand = self.expr_into_operand(variant, bid, None);

        let mut assertions = vec![];

        let a = last_variant_operand;
        let b = Operand::Move(initial_variant);

        let variant_ty = variant.ty();
        match variant_ty.kind(self.db) {
            TypeData::Error => {}
            TypeData::Void => {}
            TypeData::Ref { .. } => todo!(),
            // a <_ b <==> a == null && b != null
            TypeData::Optional(_) => {
                assertions.push(MExpr::BinaryOp(
                    BinaryOp::eq(),
                    a,
                    Operand::Literal(hir::Literal::Null),
                ));
                assertions.push(MExpr::BinaryOp(
                    BinaryOp::ne(),
                    b,
                    Operand::Literal(hir::Literal::Null),
                ));
            }
            // a <_ b <==> a < b && 0 <= b
            TypeData::Primitive(Primitive::Int) => {
                assertions.push(MExpr::BinaryOp(BinaryOp::lt(), a, b));
                assertions.push(MExpr::BinaryOp(
                    BinaryOp::le(),
                    Operand::Literal(hir::Literal::Int(0)),
                    b,
                ));
            }
            // a <_ b <==> a == false && b == true
            TypeData::Primitive(Primitive::Bool) => {
                assertions.push(MExpr::BinaryOp(
                    BinaryOp::eq(),
                    a,
                    Operand::Literal(hir::Literal::Bool(false)),
                ));
                assertions.push(MExpr::BinaryOp(
                    BinaryOp::eq(),
                    b,
                    Operand::Literal(hir::Literal::Bool(true)),
                ));
            }
            TypeData::Builtin(builtin) => match builtin.kind(self.db) {
                BuiltinKind::Set => todo!(),
                BuiltinKind::MultiSet => todo!(),
                BuiltinKind::Map => todo!(),
                // a <_ b <==> |a| < |b|
                BuiltinKind::List => {
                    let len = |o| match o {
                        Operand::Copy(p) | Operand::Move(p) => p.project_deeper(
                            self.db,
                            &[Projection::Field(Field::Builtin(
                                BuiltinField::List(variant_ty, ListField::Len),
                                Type::int(self.db),
                            ))],
                        ),
                        Operand::Literal(_) => todo!(),
                    };

                    assertions.push(MExpr::BinaryOp(
                        BinaryOp::lt(),
                        Operand::Copy(len(a)),
                        Operand::Copy(len(b)),
                    ));
                }
                BuiltinKind::Range => todo!(),
            },
            TypeData::Adt(_) => todo!(),
            TypeData::Function { .. } => todo!(),
            TypeData::Generic(_) => todo!(),
            TypeData::Null => {
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
    fn assign(&mut self, bid: BlockId, source: Option<ExprPtr>, dest: Place, expr: MExpr) -> Place {
        self.alloc_instruction(source, bid, Instruction::Assign(dest, expr));
        dest
    }
    fn lhs_expr(
        &mut self,
        expr: ExprPtr,
        bid: BlockId,
        _target: Option<BlockId>,
    ) -> (BlockId, Place) {
        match expr.data(self.db) {
            ExprData::Literal(_) => todo!(),
            ExprData::Self_ => todo!(),
            ExprData::Ident(x) => (bid, self.var_place(x)),
            ExprData::Block(_) => todo!(),
            ExprData::NotNull(_) => todo!(),
            ExprData::Field { expr: base, field, .. } => {
                let (bid, place) = self.lhs_expr(base, bid, None);
                match field {
                    Field::AdtField(_, _) | Field::Builtin(_, _) => {
                        (bid, place.project_deeper(self.db, &[Projection::Field(field)]))
                    }
                    Field::Undefined => {
                        MirErrors::push(
                            self.db,
                            MirError::NotYetImplemented {
                                msg: "lhs_expr of field access".to_string(),
                                expr,
                                span: None,
                            },
                        );

                        (bid, place)
                    }
                }
            }
            ExprData::Adt { .. } => todo!(),
            ExprData::Missing => (bid, self.alloc_tmp(Type::error(self.db))),
            ExprData::If(_) => todo!(),
            ExprData::For { .. } => todo!(),
            ExprData::While { .. } => todo!(),
            ExprData::Call { .. } => todo!(),
            ExprData::Unary { .. } => todo!(),
            ExprData::Bin { .. } => todo!(),
            ExprData::Ref { .. } => todo!(),
            ExprData::Index { base, index } => {
                let idx = self.alloc_tmp(index.ty());
                let bid = self.expr(index, bid, None, Placement::Assign(idx));
                let (bid, place) = self.lhs_expr(base, bid, None);
                (bid, place.project_deeper(self.db, &[Projection::Index(idx.slot(), expr.ty())]))
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
        expr: ExprPtr,
        bid: &mut BlockId,
        target: Option<BlockId>,
    ) -> Operand {
        let mut tmp = None;
        *bid = self.expr(expr, *bid, target, Placement::IntoOperand(expr.ty(), &mut tmp));
        tmp.unwrap_or_else(|| Operand::Move(self.alloc_place_for_expr(expr)))
    }

    fn expr_into_place(
        &mut self,
        expr: ExprPtr,
        bid: &mut BlockId,
        target: Option<BlockId>,
    ) -> Place {
        let mut tmp = None;
        *bid = self.expr(expr, *bid, target, Placement::IntoPlace(expr.ty(), &mut tmp));
        tmp.unwrap_or_else(|| {
            let ty = expr.ty();
            self.alloc_place(Slot::Temp, ty)
        })
    }
    fn expr(
        &mut self,
        expr: ExprPtr,
        mut bid: BlockId,
        target: Option<BlockId>,
        dest: Placement,
    ) -> BlockId {
        self.hint_block_source(expr, bid);

        match expr.data(self.db) {
            ExprData::Literal(l) => {
                self.put(bid, dest, Some(expr), MExpr::Use(Operand::Literal(l)));
                bid
            }
            ExprData::Self_ => {
                if let Some(self_slot) = self.self_slot() {
                    self.put(
                        bid,
                        dest,
                        Some(expr),
                        MExpr::Use(Operand::Move(self.place(self_slot))),
                    );
                } else {
                    MirErrors::push(self.db, MirError::SelfInItemWithout { expr, span: None })
                }
                bid
            }
            ExprData::Ident(var) => {
                let var_place = self.var_place(var);
                self.put(bid, dest, Some(expr), MExpr::Use(Operand::Move(var_place)));
                bid
            }
            ExprData::Block(block) => {
                let next_bid = self.alloc_block(None);
                assert_ne!(bid, next_bid);
                self.set_terminator(bid, Terminator::goto(self.db, next_bid));
                self.block(&block, next_bid, target, dest)
            }
            ExprData::Field { expr: base, field } => match field {
                Field::AdtField(_, _) | Field::Builtin(_, _) => {
                    let tmp = self.expr_into_operand(base, &mut bid, None);
                    if let Some(place) = tmp.place() {
                        let field_projection =
                            place.project_deeper(self.db, &[Projection::Field(field)]);
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
                    if !base.ty().is_error(self.db) {
                        MirErrors::push(
                            self.db,
                            MirError::NotYetImplemented {
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
                self.expr(it, bid, target, dest)
            }
            ExprData::Adt { adt, fields } => {
                let mut operands = vec![];

                for (decl, value) in fields {
                    let tmp = self.expr_into_operand(value, &mut bid, None);
                    operands.push((decl, tmp));
                }

                let dest = match dest {
                    Placement::Ignore => self.alloc_tmp(expr.ty()),
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

                let inst = Instruction::NewAdt(dest, adt, operands);
                self.alloc_instruction(Some(expr), bid, inst);

                bid
            }
            ExprData::Missing => bid,
            ExprData::If(it) => self.if_expr(&it, bid, target, dest, expr),
            ExprData::While(it) => self.while_expr(&it, bid),
            ExprData::For(it) => self.for_expr(&it, bid, expr),
            ExprData::Call { fun, args: input_args } => {
                let (func, mut args) = match fun {
                    ExprFunction::Expr(f_expr) => self.expr_to_function(f_expr),
                    ExprFunction::Builtin(bf) => (Function::BuiltinMethod(bf), Vec::new()),
                };

                for arg in input_args {
                    let tmp = self.expr_into_operand(arg, &mut bid, None);
                    args.push(tmp);
                }

                self.put_call(expr, func, args, dest, bid, target)
            }
            ExprData::Unary { op, inner } => {
                let tmp = self.expr_into_operand(inner, &mut bid, None);
                self.put(bid, dest, Some(expr), MExpr::UnaryOp(op, tmp));
                bid
            }
            ExprData::Bin { lhs, op, rhs } => {
                match op {
                    BinaryOp::Assignment => {
                        let (mut bid, left) = self.lhs_expr(lhs, bid, None);
                        let right = self.expr_into_operand(rhs, &mut bid, None);

                        self.assign(bid, Some(expr), left, MExpr::Use(right));
                        // TODO: dest is unused? should we do anything?
                        bid
                    }
                    BinaryOp::ArithOp(ArithOp::Add) if lhs.ty().is_list(self.db) => {
                        let left = self.expr_into_operand(lhs, &mut bid, None);
                        let right = self.expr_into_operand(rhs, &mut bid, None);
                        let func = Function::ListConcat;
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
                let bk = if is_mut { BorrowKind::Mutable } else { BorrowKind::Shared };
                let p = self.expr_into_place(inner, &mut bid, None);
                self.put(bid, dest, Some(expr), MExpr::Ref(bk, p));
                bid
            }
            ExprData::Index { base, index } => {
                let func = match index.ty().kind(self.db) {
                    TypeData::Builtin(b) if b.kind(self.db) == BuiltinKind::Range => {
                        Function::RangeIndex
                    }
                    TypeData::Primitive(Primitive::Int) => Function::Index,
                    TypeData::Error => Function::Index,
                    _ => todo!("tried to index with {}", index.ty().display(self.db)),
                };
                let base_s = self.expr_into_operand(base, &mut bid, None);
                let index_s = self.expr_into_operand(index, &mut bid, None);

                self.put_call(expr, func, vec![base_s, index_s], dest, bid, target)
            }
            ExprData::List { elems } => {
                let elems =
                    elems.iter().map(|&e| self.expr_into_operand(e, &mut bid, None)).collect();
                let func = Function::List;

                self.put_call(expr, func, elems, dest, bid, target)
            }
            ExprData::Quantifier { quantifier, over, expr: q_expr } => {
                let vars = match over {
                    QuantifierOver::Vars(vars) => vars,
                    QuantifierOver::In(_, _) => {
                        unreachable!("we should desugar quantifier-in in hir")
                    }
                };

                let q_body = self.alloc_block(None);
                let vars = vars.iter().map(|var| self.alloc_quantified(*var)).collect();

                let mut q_end = q_body;
                // TODO: Do we need to consider `_q_dest`?
                let _q_dest = self.expr_into_operand(q_expr, &mut q_end, None);
                let next_bid = target.unwrap_or_else(|| self.alloc_block(None));
                assert_ne!(bid, next_bid);

                self.set_terminator(bid, Terminator::quantify(self.db, quantifier, vars, q_body));
                self.set_terminator(q_end, Terminator::quantify_end(self.db, next_bid));

                next_bid
            }
            ExprData::Result => {
                if let Some(result_slot) = self.body.result_slot() {
                    let place = self.place(result_slot);
                    self.put(bid, dest, Some(expr), MExpr::Use(Operand::Move(place)));
                } else {
                    MirErrors::push(
                        self.db,
                        MirError::ResultWithoutReturnSlot { expr, span: None },
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
                let func = Function::Range(kind);

                let args = [lhs, rhs]
                    .into_iter()
                    .flatten()
                    .map(|a| self.expr_into_operand(a, &mut bid, None))
                    .collect();

                self.put_call(expr, func, args, dest, bid, target)
            }
            ExprData::Return(it) => {
                if let Some(inner) = it {
                    let result_slot = if let Some(result_slot) = self.body.result_slot() {
                        result_slot
                    } else {
                        MirErrors::push(
                            self.db,
                            MirError::ResultWithoutReturnSlot { expr, span: None },
                        );
                        todo!()
                        // self.alloc_slot(Slot::Result, expr_ty)
                    };
                    let result_operand = self.expr_into_operand(inner, &mut bid, None);
                    let result_place = self.place(result_slot);
                    self.assign(bid, Some(expr), result_place, MExpr::Use(result_operand));
                    // TODO: dest is unused?
                }
                self.set_terminator(bid, Terminator::returns(self.db));
                target.unwrap_or_else(|| self.alloc_block(None))
            }
            ExprData::Builtin(b) => match b {
                BuiltinExpr::RangeMin(r) => {
                    let r = self.expr_into_operand(r, &mut bid, None);
                    let func = Function::RangeMin;
                    self.put_call(expr, func, vec![r], dest, bid, target)
                }
                BuiltinExpr::RangeMax(r) => {
                    let r = self.expr_into_operand(r, &mut bid, None);
                    let func = Function::RangeMax;
                    self.put_call(expr, func, vec![r], dest, bid, target)
                }
                BuiltinExpr::InRange(idx, r) => {
                    let idx = self.expr_into_operand(idx, &mut bid, None);
                    let r = self.expr_into_operand(r, &mut bid, None);
                    let func = Function::InRange;
                    self.put_call(expr, func, vec![idx, r], dest, bid, target)
                }
            },
        }
    }
    fn expr_to_function(&mut self, expr: ExprPtr) -> (Function, Vec<Operand>) {
        match expr.data(self.db) {
            ExprData::Ident(var) => {
                let id = Function::Named(var);
                (id, vec![])
            }
            ExprData::Field { .. } => {
                todo!("trying to call a field: {:?}", expr)
                // todo!("trying to call a field: {}", pretty::expr(self.cx, self.db, expr))
            }
            _ => todo!("trying to call {:?}", expr),
            // _ => todo!("trying to call {}", pretty::expr(self.cx, self.db, expr)),
        }
    }
    fn if_expr(
        &mut self,
        it: &IfExpr,
        mut bid: BlockId,
        target: Option<BlockId>,
        dest: Placement,
        _expr_for_source_span: ExprPtr,
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
            self.set_terminator(then_block_final, Terminator::goto(self.db, final_block));
        }
        if else_block_final != final_block {
            assert_ne!(else_block_final, final_block);
            self.set_terminator(else_block_final, Terminator::goto(self.db, final_block));
        }
        self.set_terminator(
            bid,
            Terminator::switch(self.db, cond, SwitchTargets::new([(1, then_block)], else_block)),
        );
        final_block
    }

    // TODO: perhaps remove this, since for-loops should be desugared into while loops
    fn for_expr(&mut self, _it: &ForExpr, bid: BlockId, _expr: ExprPtr) -> BlockId {
        bid
    }

    fn while_expr(&mut self, it: &WhileExpr, mut bid: BlockId) -> BlockId {
        let cond_block = self.alloc_block(None);
        assert_ne!(bid, cond_block);
        self.set_terminator(bid, Terminator::goto(self.db, cond_block));
        bid = cond_block;
        let cond_place = self.alloc_tmp(Type::bool(self.db));
        bid = self.expr(it.expr, bid, None, Placement::Assign(cond_place));
        let cond_inv_bid = {
            let cond_inv_bid = self.alloc_block(None);
            let mut end_bid = cond_inv_bid;
            let inv_result = self.expr_into_operand(it.expr, &mut end_bid, None);
            let some_place = self.alloc_place(Slot::Temp, Type::bool(self.db));
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
        self.set_block_invariants(cond_bid_last, invariants);
        let body_bid = self.alloc_block(None);
        let mut next_bid = body_bid;
        let variant_slot = match it.decreases {
            Decreases::Unspecified => None,
            Decreases::Expr(variant) => {
                let variant_slot = self.alloc_tmp(variant.ty());
                next_bid = self.expr(variant, next_bid, None, Placement::Assign(variant_slot));
                Some(variant_slot)
            }
            Decreases::Inferred => None,
        };
        let mut body_bid_last = self.expr(it.body, next_bid, None, Placement::Ignore);
        if let (Decreases::Expr(variant), Some(variant_slot)) = (it.decreases, variant_slot) {
            self.emit_decreases_assertion(variant_slot, variant, &mut body_bid_last);
        }
        let exit_bid = self.alloc_block(None);
        assert_ne!(body_bid_last, cond_block);
        self.set_terminator(body_bid_last, Terminator::goto(self.db, cond_block));
        self.set_terminator(
            cond_bid_last,
            Terminator::switch(
                self.db,
                Operand::Copy(cond_place),
                SwitchTargets::new([(1, body_bid)], exit_bid),
            ),
        );
        exit_bid
    }
}
