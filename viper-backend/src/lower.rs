use std::{
    cmp::Ordering,
    collections::{HashSet, VecDeque},
    io::Write,
    process::Stdio,
};

use derive_new::new;
use itertools::Either;
use la_arena::{Arena, ArenaMap, Idx};
use miette::Diagnostic;
use mist_core::{
    hir::{
        self, pretty, Else, ExprIdx, IfExpr, ItemContext, ItemSourceMap, Type, VariableIdx,
        VariableRef,
    },
    mir::{self, SlotId},
};
use mist_syntax::{
    ast::operators::{ArithOp, BinaryOp, CmpOp, LogicOp},
    SourceSpan,
};
use silvers::{
    expression::{
        AbstractLocalVar, BinOp, Exp, FieldAccess, LocalVar, LocationAccess, ResourceAccess,
        SeqExp, UnOp,
    },
    program::{Field, LocalVarDecl},
    typ::Type as VTy,
};
use thiserror::Error;
use tracing::{error, info};

use crate::gen::{VExpr, VExprId, ViperSourceMap, ViperWriter};

#[derive(Debug, Diagnostic, Clone, Error)]
pub enum ViperLowerError {
    #[error("not yet implemented: {msg}")]
    NotYetImplemented {
        expr: Option<ExprIdx>,
        msg: String,
        #[label]
        label: Option<SourceSpan>,
    },
    #[error("a block did not have a tail-expr")]
    BlockWithoutTailExpr,
    #[error("a impure expression was found in pure lowering: {msg}")]
    ImpureExpressionInPure { expr: Option<ExprIdx>, msg: String },
    #[error("pure if-statement did not have an else branch")]
    IfStatementWithoutElseInPure,
    #[error("the expression and associated type was inconsistent")]
    ExprAndTypeMismatch,
}

impl ViperLowerError {
    pub fn spanned(self, source_map: &ItemSourceMap) -> Self {
        match self {
            ViperLowerError::NotYetImplemented {
                expr: Some(expr),
                msg,
                label: _,
            } => ViperLowerError::NotYetImplemented {
                expr: Some(expr),
                msg,
                label: Some(source_map.expr_span(expr)),
            },
            x => x,
        }
    }
}

#[salsa::accumulator]
pub struct ViperLowerErrors(ViperLowerError);

#[derive(new)]
pub struct ViperLower<'a> {
    db: &'a dyn crate::Db,
    cx: &'a ItemContext,
    #[new(default)]
    pub(crate) arena: Arena<VExpr>,
    #[new(default)]
    source_map: ViperSourceMap,
}

impl ViperLower<'_> {
    pub fn lower_variable(&mut self, var: VariableIdx) -> Result<LocalVar, ViperLowerError> {
        let name = self.cx.var_ident(var);
        let idx = var.into_raw();
        let ty = self.cx.var_ty(var);
        Ok(LocalVar {
            name: format!("{name}_{idx}"),
            typ: self.lower_ty(ty)?,
        })
    }
    pub fn lower_ty(&mut self, ty: Type) -> Result<VTy, ViperLowerError> {
        let todo = |ty| -> Result<VTy, ViperLowerError> {
            let err = ViperLowerError::NotYetImplemented {
                expr: None,
                msg: format!("type lowering of {}", pretty::ty(self.cx, self.db, ty)),
                label: ty.span(self.db),
            };
            error!("failed to lower: {err}");
            ViperLowerErrors::push(self.db, err.clone());
            Err(err)
        };

        Ok(match ty.strip_ghost(self.db).data(self.db) {
            hir::TypeData::Error => return todo(ty),
            hir::TypeData::Void => return todo(ty),
            hir::TypeData::Ghost(_) => return todo(ty),
            hir::TypeData::Ref { is_mut, inner } => return todo(ty),
            hir::TypeData::List(inner) => {
                let inner = self.lower_ty(*inner)?;
                VTy::Seq {
                    element_type: Box::new(inner),
                }
            }
            hir::TypeData::Optional(_) => return todo(ty),
            hir::TypeData::Primitive(p) => match p {
                hir::Primitive::Int => VTy::int(),
                hir::Primitive::Bool => VTy::bool(),
            },
            hir::TypeData::Struct(_) => return todo(ty),
            hir::TypeData::Null => return todo(ty),
            hir::TypeData::Function {
                attrs,
                name,
                params,
                return_ty,
            } => return todo(ty),
            hir::TypeData::Range(_) => return todo(ty),
        })
    }
    // TODO: The return type should be something different
    pub fn lower_expr(&mut self, id: ExprIdx) -> Result<VExprId, ViperLowerError> {
        let todo = |e| -> Result<VExprId, ViperLowerError> {
            let err = ViperLowerError::NotYetImplemented {
                expr: Some(e),
                msg: format!(
                    "non-pure lowering of {}",
                    pretty::expr(self.cx, self.db, e,)
                ),
                label: None,
            };
            error!("failed to lower: {err}");
            ViperLowerErrors::push(self.db, err.clone());
            Err(err)
        };

        let exp = match &self.cx.expr(id).data {
            hir::ExprData::Literal(l) => lower_lit(l),
            hir::ExprData::Ident(v) => self.lower_ident(v)?,
            hir::ExprData::Block(_) => return todo(id),
            hir::ExprData::Field {
                expr,
                field_name,
                field,
            } => return todo(id),
            hir::ExprData::Struct {
                struct_declaration,
                struct_span,
                fields,
            } => return todo(id),
            hir::ExprData::Missing => return todo(id),
            hir::ExprData::If(_) => return todo(id),
            hir::ExprData::Call { expr, args } => return todo(id),
            hir::ExprData::Unary { op, inner } => return todo(id),
            hir::ExprData::Bin { lhs, op, rhs } => return todo(id),
            hir::ExprData::Ref { is_mut, expr } => return todo(id),
            hir::ExprData::Index { base, index } => return todo(id),
            hir::ExprData::List { elems } => return todo(id),
            hir::ExprData::Quantifier {
                quantifier,
                params,
                expr,
            } => return todo(id),
            hir::ExprData::Result => return todo(id),
            hir::ExprData::Range { lhs, rhs } => return todo(id),
            hir::ExprData::Return(_) => return todo(id),
        };
        Ok(self.alloc(id, VExpr::new(exp)))
    }
    pub fn lower_expr_pure(
        &mut self,
        skip_impure: bool,
        id: ExprIdx,
    ) -> Result<VExprId, ViperLowerError> {
        let todo = |e| -> Result<VExprId, ViperLowerError> {
            let err = ViperLowerError::NotYetImplemented {
                expr: Some(e),
                msg: format!("pure lowering of {}", pretty::expr(self.cx, self.db, e,)),
                label: None,
            };
            error!("failed to lower: {err}");
            ViperLowerErrors::push(self.db, err.clone());
            Err(err)
        };

        let expr_ty = self.cx.expr(id).ty;
        let exp = match &self.cx.expr(id).data {
            hir::ExprData::Literal(l) => lower_lit(l),
            hir::ExprData::Ident(v) => self.lower_ident(v)?,
            hir::ExprData::Block(block) => return self.lower_block_pure(skip_impure, block),
            hir::ExprData::Return(_) => return todo(id),
            hir::ExprData::Field {
                expr,
                field_name,
                field: _,
            } => {
                let rcr = self.lower_expr_pure(skip_impure, *expr)?;
                self.lower_field_access(skip_impure, rcr, expr_ty, field_name)?
            }
            hir::ExprData::Struct { .. } => return todo(id),
            hir::ExprData::Missing => return todo(id),
            hir::ExprData::If(if_expr) => self.lower_if_expr_pure(skip_impure, if_expr)?,
            hir::ExprData::Call { expr, args } => {
                let args: Result<_, _> = args
                    .iter()
                    .map(|e| self.lower_expr_pure(skip_impure, *e))
                    .collect();
                let args: Vec<_> = args?;

                // HACK: We allow expr in arbitrary locations, but syntactically they cannot be
                // constructed ATM, so we just pretty print the expr to get the name.
                // let expr = self.lower_expr_pure(skip_impure,*expr)?;
                let funcname = pretty::expr(self.cx, self.db, *expr);
                Exp::FuncApp { funcname, args }
            }
            hir::ExprData::Unary { op, inner } => return todo(id),
            hir::ExprData::Bin { lhs, op, rhs } => {
                let left = self.lower_expr_pure(skip_impure, *lhs)?;
                let right = self.lower_expr_pure(skip_impure, *rhs)?;
                let op =
                    lower_binop(op).ok_or_else(|| ViperLowerError::ImpureExpressionInPure {
                        expr: Some(id),
                        msg: pretty::expr(self.cx, self.db, id),
                    })?;
                Exp::bin(left, op, right)
            }
            hir::ExprData::Ref { is_mut: _, expr } => {
                return self.lower_expr_pure(skip_impure, *expr)
            }
            hir::ExprData::Index { base, index } => {
                let base = self.lower_expr_pure(skip_impure, *base)?;
                match &self.cx.expr(*index).data {
                    hir::ExprData::Range { lhs, rhs } => {
                        let low = lhs
                            .map(|id| self.lower_expr_pure(skip_impure, id))
                            .transpose()?;
                        let high = rhs
                            .map(|id| self.lower_expr_pure(skip_impure, id))
                            .transpose()?;
                        match lower_seq_range_index(low, high, base) {
                            Ok(e) => match e {
                                Either::Left(exp) => exp,
                                Either::Right(id) => return Ok(id),
                            },
                            Err(()) => return todo(id),
                        }
                    }
                    _ => {
                        let index = self.lower_expr_pure(skip_impure, *index)?;
                        Exp::Seq(SeqExp::Index {
                            s: base,
                            idx: index,
                        })
                    }
                }
            }
            hir::ExprData::List { elems } => {
                let elems: Result<_, _> = elems
                    .iter()
                    .map(|e| self.lower_expr_pure(skip_impure, *e))
                    .collect();
                let elems: Vec<_> = elems?;
                self.lower_list(elems, expr_ty)?
            }
            hir::ExprData::Quantifier {
                quantifier,
                params,
                expr,
            } => {
                let variables = params
                    .iter()
                    .map(|param| {
                        Ok(LocalVarDecl {
                            name: self.lower_variable(param.name)?.to_string(),
                            typ: self.lower_ty(param.ty)?,
                        })
                    })
                    .collect::<Result<_, _>>()?;
                let exp = self.lower_expr_pure(skip_impure, *expr)?;
                let triggers = vec![];
                match quantifier {
                    hir::Quantifier::Forall => Exp::forall(variables, triggers, exp),
                    hir::Quantifier::Exists => Exp::exists(variables, triggers, exp),
                }
            }
            hir::ExprData::Result => self.lower_result(expr_ty)?,
            hir::ExprData::Range { lhs, rhs } => return todo(id),
        };
        Ok(self.alloc(id, VExpr::new(exp)))
    }

    fn lower_list(
        &mut self,
        elems: Vec<VExprId>,
        expr_ty: Type,
    ) -> Result<Exp<VExprId>, ViperLowerError> {
        Ok(if elems.is_empty() {
            let ty = match expr_ty.data(self.db) {
                hir::TypeData::List(elem_ty) => *elem_ty,
                _ => return Err(ViperLowerError::ExprAndTypeMismatch),
            };
            let elem_typ = self.lower_ty(ty)?;
            Exp::Seq(SeqExp::Empty { elem_typ })
        } else {
            Exp::Seq(SeqExp::Explicit { elems })
        })
    }

    fn lower_result(&mut self, expr_ty: Type) -> Result<Exp<VExprId>, ViperLowerError> {
        Ok(Exp::AbstractLocalVar(AbstractLocalVar::Result {
            typ: self.lower_ty(expr_ty)?,
        }))
    }

    fn lower_field_access(
        &mut self,
        skip_impure: bool,
        rcr: VExprId,
        expr_ty: Type,
        field_name: &hir::Ident,
    ) -> Result<Exp<VExprId>, ViperLowerError> {
        let ty = self.lower_ty(expr_ty)?;
        Ok(Exp::LocationAccess(ResourceAccess::Location(
            LocationAccess::Field(FieldAccess::new(
                rcr,
                Field::new(field_name.to_string(), ty),
            )),
        )))
    }

    fn lower_ident(&mut self, v: &VariableRef) -> Result<Exp<VExprId>, ViperLowerError> {
        Ok(Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(
            self.lower_variable(v.idx())?,
        )))
    }

    pub fn lower_if_expr_pure(
        &mut self,
        skip_impure: bool,
        if_expr: &IfExpr,
    ) -> Result<Exp<VExprId>, ViperLowerError> {
        let condition = self.lower_expr_pure(skip_impure, if_expr.condition)?;
        let then_body = self.lower_block_pure(skip_impure, &if_expr.then_branch)?;
        let else_expr = match if_expr.else_branch.as_deref() {
            Some(Else::Block(block)) => self.lower_block_pure(skip_impure, block)?,
            Some(Else::If(nested)) => {
                let exp = self.lower_if_expr_pure(skip_impure, nested)?;
                // NOTE: Since we don't have a ExprIdx to link this to, we just
                // allocate it plainly
                self.arena.alloc(VExpr::new(exp))
            }
            None => return Err(ViperLowerError::IfStatementWithoutElseInPure),
        };

        Ok(Exp::Cond {
            cond: condition,
            thn: then_body,
            els: else_expr,
        })
    }
    pub fn lower_block_pure(
        &mut self,
        skip_impure: bool,
        block: &hir::Block,
    ) -> Result<VExprId, ViperLowerError> {
        if let Some(tail) = block.tail_expr {
            if block.stmts.is_empty() {
                self.lower_expr_pure(skip_impure, tail)
            } else {
                let mut acc = self.lower_expr_pure(skip_impure, tail)?;

                for stmt in block.stmts.iter().rev() {
                    match &stmt.data {
                        hir::StatementData::Expr(_) => continue,
                        hir::StatementData::Let {
                            variable,
                            initializer,
                            ..
                        } => {
                            let variable = self.lower_variable(variable.idx())?;
                            let exp = self.lower_expr_pure(skip_impure, *initializer)?;
                            acc = self.arena.alloc(VExpr::new(Exp::Let {
                                variable: LocalVarDecl::new(variable.name, variable.typ),
                                exp,
                                body: acc,
                            }));
                        }
                        hir::StatementData::While { .. } => continue,
                        hir::StatementData::Assertion { .. } => continue,
                    }
                }

                Ok(acc)
            }
        } else {
            Err(ViperLowerError::BlockWithoutTailExpr)
        }
    }

    fn alloc(&mut self, expr: ExprIdx, v: VExpr) -> VExprId {
        let id = self.arena.alloc(v);
        self.source_map.expr_map.insert(expr, id);
        self.source_map.expr_map_back.insert(id, expr);
        id
    }
}

fn lower_seq_range_index(
    low: Option<VExprId>,
    high: Option<VExprId>,
    base: VExprId,
) -> Result<Either<Exp<VExprId>, VExprId>, ()> {
    Ok(match (low, high) {
        (None, None) => Either::Right(base),
        (None, Some(high)) => Either::Left(Exp::Seq(SeqExp::Take { s: base, n: high })),
        (Some(low), None) => Either::Left(Exp::Seq(SeqExp::Drop { s: base, n: low })),
        (Some(low), Some(high)) => return Err(()),
    })
}

fn lower_binop(op: &BinaryOp) -> Option<BinOp> {
    use BinOp::*;

    Some(match op {
        BinaryOp::LogicOp(op) => match op {
            LogicOp::Or => Or,
            LogicOp::And => And,
        },
        BinaryOp::CmpOp(op) => match op {
            CmpOp::Eq { negated: true } => NeCmp,
            CmpOp::Eq { negated: false } => EqCmp,
            CmpOp::Ord { ordering, strict } => match (ordering, strict) {
                (Ordering::Less, true) => LtCmp,
                (Ordering::Less, false) => LeCmp,
                (Ordering::Equal, true) => EqCmp,
                (Ordering::Equal, false) => EqCmp,
                (Ordering::Greater, true) => GtCmp,
                (Ordering::Greater, false) => GeCmp,
            },
        },
        BinaryOp::ArithOp(op) => match op {
            ArithOp::Add => Add,
            ArithOp::Mul => Mul,
            ArithOp::Sub => Sub,
            ArithOp::Div => Div,
            ArithOp::Rem => Mod,
            ArithOp::Shl | ArithOp::Shr | ArithOp::BitXor | ArithOp::BitOr | ArithOp::BitAnd => {
                todo!()
            }
        },
        BinaryOp::Assignment => return None,
    })
}

fn lower_lit(l: &hir::Literal) -> Exp<VExprId> {
    match l {
        hir::Literal::Null => Exp::null(),
        hir::Literal::Int(i) => Exp::int(*i),
        hir::Literal::Bool(b) => Exp::boolean(*b),
    }
}

pub fn lower_body_pure(
    db: &dyn crate::Db,
    program: hir::Program,
    cx: &ItemContext,
    body: &mir::Body,
) -> Option<()> {
    let result_slot = body.result_slot()?;

    if let Some(b) = body.body_block() {
        lower_block_pure(db, program, cx, body, b, result_slot);
    }

    None
}

fn lower_block_pure(
    db: &dyn crate::Db,
    program: hir::Program,
    cx: &ItemContext,
    body: &mir::Body,
    block: mir::BlockId,
    target: mir::SlotId,
) -> Option<VExprId> {
    let g = mir::analysis::compute_dataflow(body);

    let (start_node, new_g) = g.flow_from(body, target)?;
    let pretty_g = mir::analysis::pretty_graph(db, program, cx, body, &new_g);

    let mut traversal = mir::analysis::petgraph::visit::DfsPostOrder::new(&pretty_g, start_node);
    while let Some(next) = traversal.next(&pretty_g) {
        // info!("{}", pretty_g.node_weight(next).unwrap());
    }

    println!("{}", body.serialize(db, program, cx));

    let dot = mir::analysis::pretty_dot(&pretty_g);
    // dot_imgcat(dot);

    None
}

pub fn lower_body_purest(
    db: &dyn crate::Db,
    program: hir::Program,
    cx: &ItemContext,
    body: &mir::Body,
) -> Option<()> {
    let mut lower = PureLower::new(cx, body);
    if let Some(b) = body.body_block() {
        match lower.final_block(b) {
            Ok(b) => {
                use crate::gen::ViperWriter;

                let mut writer = ViperWriter::new(&lower.arena);
                writer.emit(&b);
                let output = writer.finish();
                println!("{}", output.buf);
                // ViperHints::push(db, ViperHint::new(source_map.expr_span(e), output.buf));
            }
            Err(()) => {}
        }
    }
    None
}

#[derive(Debug, Default)]
struct SourceMap {
    inst_expr: ArenaMap<mir::InstructionId, VExprId>,
    inst_expr_back: ArenaMap<VExprId, mir::InstructionId>,
}

#[derive(new, Debug)]
struct PureLower<'a> {
    cx: &'a hir::ItemContext,
    body: &'a mir::Body,
    #[new(default)]
    arena: Arena<VExpr>,
    #[new(default)]
    source_map: SourceMap,
}

impl PureLower<'_> {
    fn alloc(&mut self, inst_id: mir::InstructionId, vexpr: VExpr) -> VExprId {
        let id = self.arena.alloc(vexpr);
        self.source_map.inst_expr.insert(inst_id, id);
        self.source_map.inst_expr_back.insert(id, inst_id);
        id
    }
    fn block(&mut self, block: mir::BlockId) -> Result<(VExprId, mir::SlotId), ()> {
        self.body[block]
            .instructions()
            .iter()
            .copied()
            .try_rfold(None, |acc, inst| {
                Ok(match &self.body[inst] {
                    mir::Instruction::Assign(x, e) => match acc {
                        Some((body, target)) => {
                            let variable = self.slot_to_decl(*x);
                            let exp = self.expr(inst, e)?;
                            let vexp = Exp::Let {
                                variable,
                                exp,
                                body,
                            };
                            Some((self.alloc(inst, VExpr::new(vexp)), target))
                        }
                        None => Some((self.expr(inst, e)?, *x)),
                    },
                    &mir::Instruction::If(cond, then_b, else_b) => {
                        let (then_e, then_t) = self.block(then_b)?;
                        let (else_e, else_t) = self.block(else_b)?;
                        let exp = Exp::new_cond(self.slot_to_ref(cond), then_e, else_e);
                        match acc {
                            Some((tail, last_target)) => {
                                let exp = Exp::new_let(
                                    self.slot_to_decl(then_t),
                                    self.alloc(inst, VExpr::new(exp)),
                                    tail,
                                );
                                Some((self.arena.alloc(VExpr::new(exp)), last_target))
                            }
                            None => Some((self.alloc(inst, VExpr::new(exp)), then_t)),
                        }
                    }
                    _ => acc,
                })
            })
            .transpose()
            .unwrap_or(Err(()))
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
    fn slot_to_ref(&mut self, s: SlotId) -> VExprId {
        let exp = match &self.body[s] {
            mir::Slot::Temp | mir::Slot::Var(_) => {
                Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(self.slot_to_var(s)))
            }
            mir::Slot::Literal(l) => lower_lit(l),
            mir::Slot::Result => Exp::AbstractLocalVar(AbstractLocalVar::Result {
                typ: VTy::internal_type(),
            }),
        };

        self.arena.alloc(VExpr::new(exp))
    }

    fn expr(&mut self, inst: mir::InstructionId, e: &mir::MExpr) -> Result<VExprId, ()> {
        let exp = match e {
            mir::MExpr::Literal(l) => lower_lit(l),
            mir::MExpr::Call(fid, args) => self.function(*fid, args)?,
            mir::MExpr::Field(rcr, f) => match &f.parent {
                hir::FieldParent::Struct(_) => {
                    error!("lower struct field: {f:?}");
                    return Err(());
                }
                hir::FieldParent::List(_) => match f.name.as_str() {
                    "len" => Exp::Seq(SeqExp::new_length(self.slot_to_ref(*rcr))),
                    _ => {
                        error!("lower list field: {f:?}");
                        return Err(());
                    }
                },
            },
            mir::MExpr::Struct(_, _) => {
                error!("lower struct");
                return Err(());
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
                let (exp, _target) = self.block(*body)?;
                // TODO: target should be _q_target
                let triggers = vec![];
                match q {
                    hir::Quantifier::Forall => Exp::forall(variables, triggers, exp),
                    hir::Quantifier::Exists => Exp::exists(variables, triggers, exp),
                }
            }
        };
        Ok(self.alloc(inst, VExpr::new(exp)))
    }

    fn function(&mut self, fid: mir::FunctionId, args: &[mir::SlotId]) -> Result<Exp<VExprId>, ()> {
        use mist_syntax::ast::operators::UnaryOp;

        Ok(match &*self.body[fid] {
            mir::FunctionData::Named(v) => Exp::new_func_app(
                self.cx.var_ident(*v).to_string(),
                args.iter().map(|s| self.slot_to_ref(*s)).collect(),
            ),
            mir::FunctionData::BinaryOp(op) => {
                let op = lower_binop(op).expect("assignment should have been filtered out by now");
                let lhs = self.slot_to_ref(args[0]);
                let rhs = self.slot_to_ref(args[1]);
                Exp::new_bin(op, lhs, rhs)
            }
            mir::FunctionData::UnaryOp(op) => {
                let op = match op {
                    UnaryOp::Not => UnOp::Not,
                    UnaryOp::Neg => UnOp::Minus,
                };
                let exp = self.slot_to_ref(args[0]);
                Exp::new_un(op, exp)
            }
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

    fn final_block(&mut self, b: mir::BlockId) -> Result<VExprId, ()> {
        let (exp, _target) = self.block(b)?;
        // TODO: Target should be result
        Ok(exp)
    }
}

// dot -T png | imgcat
fn dot_imgcat(dot: String) {
    let dot_cmd = std::process::Command::new("dot")
        .args([
            "-Gmargin=0.7",
            "-Gbgcolor=#ffffff00",
            "-Gcolor=white",
            "-Gfontcolor=white",
            "-Ncolor=white",
            "-Nfontcolor=white",
            "-Ecolor=white",
            "-Efontcolor=white",
        ])
        .args(["-T", "png"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let imgcat = std::process::Command::new("imgcat")
        .stdin(Stdio::from(dot_cmd.stdout.unwrap()))
        .stdout(Stdio::inherit())
        .spawn()
        .unwrap();

    dot_cmd.stdin.unwrap().write_all(dot.as_bytes()).unwrap();

    imgcat.wait_with_output().unwrap();
}
