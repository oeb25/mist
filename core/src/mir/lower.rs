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
    InstructionId, MExpr, RangeKind, Slot, SlotId,
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

    let body_block = cx.body_expr().map(|body| {
        let return_slot = lower.alloc_slot(Slot::Result);
        lower.expr_to_block(body, Some(return_slot))
    });

    lower.body.body_block = body_block;

    lower.finish()
}

#[derive(new)]
struct MirLower<'a> {
    db: &'a dyn crate::Db,
    cx: &'a ItemContext,

    #[new(default)]
    instructions: Vec<InstructionId>,
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
        instruction: Instruction,
    ) -> InstructionId {
        let id = self.body.instructions.alloc(instruction);
        self.instructions.push(id);
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
    fn blocked(
        &mut self,
        expr: Option<ExprIdx>,
        compute_block: impl FnOnce(&mut Self) -> Option<SlotId>,
    ) -> BlockId {
        let prev = mem::take(&mut self.instructions);

        let dest = compute_block(self);

        let instructions = mem::replace(&mut self.instructions, prev);

        self.alloc_block(expr, Block { instructions, dest })
    }
}
impl MirLower<'_> {
    fn expr_to_block(&mut self, expr: ExprIdx, dest: Option<SlotId>) -> BlockId {
        self.blocked(Some(expr), |this| match &this.cx.expr(expr).data {
            ExprData::Block(block) => {
                for stmt in &block.stmts {
                    this.stmt(stmt);
                }
                if let Some(tail) = block.tail_expr {
                    let dest = this.expr(tail, dest);
                    Some(dest)
                } else {
                    dest
                }
            }
            _ => Some(this.expr(expr, dest)),
        })
    }
    fn block(
        &mut self,
        block: &hir::Block,
        dest: Option<SlotId>,
        post: impl FnOnce(&mut Self),
    ) -> BlockId {
        self.blocked(None, |this| {
            for stmt in &block.stmts {
                this.stmt(stmt);
            }
            if let Some(tail) = block.tail_expr {
                let dest = this.expr(tail, dest);
                post(this);
                Some(dest)
            } else {
                post(this);
                dest
            }
        })
    }
    fn stmt(&mut self, stmt: &Statement) {
        match &stmt.data {
            StatementData::Expr(expr) => {
                self.expr(*expr, None);
            }
            StatementData::Let {
                variable,
                explicit_ty: _,
                initializer,
            } => {
                let dest = self.alloc_slot(Slot::from_var(variable.idx()));
                self.expr(*initializer, Some(dest));
            }
            StatementData::While {
                expr,
                invariants,
                decreases,
                body,
            } => {
                let cond_slot = self.alloc_tmp();
                self.expr(*expr, Some(cond_slot));

                let invariants = invariants
                    .iter()
                    .flatten()
                    .map(|inv| self.expr_to_block(*inv, None))
                    .collect();

                let body = self.block(body, None, |this| {
                    this.expr(*expr, Some(cond_slot));
                });

                self.alloc_instruction(None, Instruction::While(cond_slot, invariants, body));
            }
            StatementData::Assertion { kind, exprs } => {
                for expr in exprs {
                    let dest = self.expr(*expr, None);
                    self.alloc_instruction(None, Instruction::Assertion(kind.clone(), dest));
                }
            }
        }
    }
    fn assign(&mut self, source: Option<ExprIdx>, dest: Option<SlotId>, expr: MExpr) -> SlotId {
        let dest = dest.unwrap_or_else(|| self.alloc_tmp());
        self.alloc_instruction(source, Instruction::Assign(dest, expr));
        dest
    }
    fn expr(&mut self, expr: ExprIdx, dest: Option<SlotId>) -> SlotId {
        match &self.cx.expr(expr).data {
            ExprData::Literal(l) => {
                let l_slot = self.alloc_slot(Slot::Literal(l.clone()));
                if let Some(dest) = dest {
                    self.assign(Some(expr), Some(dest), MExpr::Slot(l_slot))
                } else {
                    l_slot
                }
            }
            ExprData::Ident(var) => {
                let var_slot = self.var_slot(var.idx());
                if let Some(dest) = dest {
                    self.assign(Some(expr), Some(dest), MExpr::Slot(var_slot))
                } else {
                    var_slot
                }
            }
            ExprData::Block(block) => {
                let bid = self.block(block, dest, |_| {});
                // TODO: This is a bit strange?
                self.body.blocks[bid]
                    .dest
                    .unwrap_or_else(|| self.alloc_tmp())
            }
            ExprData::Field {
                expr: base,
                field_name: _,
                field,
            } => {
                if let Some(field) = field {
                    let base = self.expr(*base, None);
                    self.assign(Some(expr), dest, MExpr::Field(base, field.clone()))
                } else {
                    todo!()
                }
            }
            ExprData::Struct {
                struct_declaration,
                struct_span: _,
                fields,
            } => {
                let fields = fields
                    .iter()
                    .map(|f| (f.decl.clone(), self.expr(f.value, None)))
                    .collect();
                self.assign(Some(expr), dest, MExpr::Struct(*struct_declaration, fields))
            }
            ExprData::Missing => dest.unwrap_or_else(|| self.alloc_tmp()),
            ExprData::If(it) => {
                let dest = dest.unwrap_or_else(|| self.alloc_tmp());
                self.if_expr(it, dest, expr)
            }
            ExprData::Call {
                expr: f_expr,
                args: input_args,
            } => {
                let (function, mut args) = self.expr_to_function(*f_expr);

                for arg in input_args {
                    args.push(self.expr(*arg, None));
                }

                self.assign(Some(expr), dest, MExpr::Call(function, args))
            }
            ExprData::Unary { op, inner } => {
                let arg = self.expr(*inner, None);
                let function = self.alloc_function(Function::new(FunctionData::UnaryOp(*op)));

                self.assign(Some(expr), dest, MExpr::Call(function, vec![arg]))
            }
            ExprData::Bin { lhs, op, rhs } => {
                if let BinaryOp::Assignment = op {
                    // TODO: lhs should really be computed in a lhs fashion
                    let lhs = self.expr(*lhs, None);
                    let rhs = self.expr(*rhs, None);

                    self.assign(Some(expr), Some(lhs), MExpr::Slot(rhs));
                    // TODO: What should we even assign here?
                    dest.unwrap_or_else(|| self.alloc_tmp())
                } else {
                    let lhs = self.expr(*lhs, None);
                    let rhs = self.expr(*rhs, None);

                    let function = self.alloc_function(Function::new(FunctionData::BinaryOp(*op)));
                    self.assign(Some(expr), dest, MExpr::Call(function, vec![lhs, rhs]))
                }
            }
            ExprData::Ref { is_mut, expr } => todo!(),
            ExprData::Index { base, index } => {
                let f = match &self.cx.expr(*index).ty.strip_ghost(self.db).data(self.db) {
                    hir::TypeData::Range(_) => FunctionData::RangeIndex,
                    hir::TypeData::Primitive(hir::Primitive::Int) => FunctionData::Index,
                    ty => todo!("tried to index with {ty:?}"),
                };
                let base = self.expr(*base, None);
                let index = self.expr(*index, None);
                let function = self.alloc_function(Function::new(f));

                self.assign(Some(expr), dest, MExpr::Call(function, vec![base, index]))
            }
            ExprData::List { elems } => {
                let elems = elems.iter().map(|e| self.expr(*e, None)).collect();
                let function = self.alloc_function(Function::new(FunctionData::List));

                self.assign(Some(expr), dest, MExpr::Call(function, elems))
            }
            ExprData::Quantifier {
                quantifier,
                params,
                expr: q_expr,
            } => {
                let q_dest = self.alloc_tmp();
                let q_body = self.expr_to_block(*q_expr, Some(q_dest));
                let params = params
                    .iter()
                    .map(|param| self.alloc_slot(Slot::from_var(param.name)))
                    .collect();
                let mexpr = MExpr::Quantifier(q_dest, *quantifier, params, q_body);

                self.assign(Some(expr), dest, mexpr)
            }
            ExprData::Result => {
                let result_slot = self.alloc_slot(Slot::Result);

                if let Some(dest) = dest {
                    self.assign(Some(expr), Some(dest), MExpr::Slot(result_slot))
                } else {
                    result_slot
                }
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
                    .map(|&a| self.expr(a, None))
                    .collect();

                self.assign(Some(expr), dest, MExpr::Call(function, args))
            }
            ExprData::Return(it) => {
                match it {
                    Some(inner) => {
                        let result_slot = self.alloc_slot(Slot::Result);
                        self.expr(*inner, Some(result_slot));
                    }
                    None => {}
                }
                self.alloc_instruction(Some(expr), Instruction::Return);
                dest.unwrap_or_else(|| self.alloc_tmp())
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
    fn if_expr(&mut self, it: &IfExpr, dest: SlotId, expr: ExprIdx) -> SlotId {
        let cond = self.expr(it.condition, None);
        let then_block = self.block(&it.then_branch, Some(dest), |_| {});
        let else_block = match it.else_branch.as_deref() {
            Some(Else::Block(else_block)) => self.block(else_block, Some(dest), |_| {}),
            Some(Else::If(nested)) => self.blocked(None, |this| {
                this.if_expr(nested, dest, expr);
                Some(dest)
            }),
            None => self.blocked(None, |_| Some(dest)),
        };
        self.alloc_instruction(Some(expr), Instruction::If(cond, then_block, else_block));
        dest
    }
}
