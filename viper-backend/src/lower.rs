use std::{cmp::Ordering, collections::HashMap};

use derive_new::new;
use la_arena::{Arena, ArenaMap};

use miette::Diagnostic;
use mist_core::{
    hir,
    mir::{self, analysis::cfg, BlockOrInstruction},
};
use mist_syntax::{
    ast::operators::{ArithOp, BinaryOp, CmpOp, LogicOp},
    SourceSpan,
};
use silvers::{
    expression::{AbstractLocalVar, BinOp, Exp, LocalVar, SeqExp, UnOp},
    program::LocalVarDecl,
    typ::Type as VTy,
};
use tracing::error;

use crate::gen::{VExpr, VExprId};

pub mod method;
pub mod pure;

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

#[derive(new)]
pub(crate) struct ViperLowerer {
    #[new(default)]
    viper_body: ViperBody,
    #[new(default)]
    source_map: ViperSourceMap,
}

impl ViperLowerer {
    pub fn body_lower<'a>(
        &'a mut self,
        db: &'a dyn crate::Db,
        cx: &'a hir::ItemContext,
        mir: &'a mir::Body,
        is_method: bool,
    ) -> BodyLower<'a> {
        BodyLower::new(
            db,
            cx,
            mir,
            is_method,
            &mut self.viper_body,
            &mut self.source_map,
        )
    }
    pub fn finish(self) -> (ViperBody, ViperSourceMap) {
        (self.viper_body, self.source_map)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ViperBody {
    arena: Arena<VExpr>,
}

impl std::ops::Index<VExprId> for ViperBody {
    type Output = VExpr;

    fn index(&self, index: VExprId) -> &Self::Output {
        &self.arena[index]
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ViperSourceMap {
    pub inst_expr: HashMap<(hir::ItemId, mir::InstructionId), VExprId>,
    pub inst_expr_back: ArenaMap<VExprId, (hir::ItemId, mir::InstructionId)>,
    pub block_expr: HashMap<(hir::ItemId, mir::BlockId), VExprId>,
    pub block_expr_back: ArenaMap<VExprId, (hir::ItemId, mir::BlockId)>,
}

impl ViperSourceMap {
    pub fn trace_exp(&self, exp: VExprId) -> Option<(hir::ItemId, mir::BlockOrInstruction)> {
        if let Some(&(item_id, instr)) = self.inst_expr_back.get(exp) {
            return Some((item_id, instr.into()));
        }
        if let Some(&(item_id, block)) = self.block_expr_back.get(exp) {
            return Some((item_id, block.into()));
        }
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error, Diagnostic)]
pub enum ViperLowerError {
    #[error("not yet implemented: {msg}")]
    NotYetImplemented {
        msg: String,
        item_id: hir::ItemId,
        block_or_inst: Option<mir::BlockOrInstruction>,
        #[label]
        span: Option<SourceSpan>,
    },
    #[error("the body did not contain any actions")]
    EmptyBody,
}

impl ViperLowerError {
    pub fn populate_spans(
        &mut self,
        f: impl Fn(hir::ItemId, mir::BlockOrInstruction) -> Option<SourceSpan>,
    ) {
        match self {
            ViperLowerError::NotYetImplemented {
                item_id,
                block_or_inst: Some(block_or_inst),
                span,
                ..
            } => {
                *span = f(*item_id, *block_or_inst);
            }
            ViperLowerError::NotYetImplemented { .. } => {}
            ViperLowerError::EmptyBody => {}
        }
    }
}

#[salsa::accumulator]
pub struct ViperLowerErrors(ViperLowerError);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ViperType {
    pub vty: VTy,
    optional: bool,
    is_mut: bool,
}

impl From<VTy> for ViperType {
    fn from(vty: VTy) -> Self {
        ViperType {
            vty,
            is_mut: false,
            optional: false,
        }
    }
}

pub struct BodyLower<'a> {
    db: &'a dyn crate::Db,
    cx: &'a hir::ItemContext,
    body: &'a mir::Body,
    viper_body: &'a mut ViperBody,
    source_map: &'a mut ViperSourceMap,
    is_method: bool,
    cfg: cfg::Cfg,
    postdominance_frontier: cfg::PostdominanceFrontier,
    postdominators: cfg::Postdominators,
    var_refs: ArenaMap<mir::SlotId, VExprId>,
    times_referenced: ArenaMap<mir::SlotId, usize>,
    inlined: ArenaMap<VExprId, VExprId>,
}

impl<'a> BodyLower<'a> {
    pub fn new(
        db: &'a dyn crate::Db,
        cx: &'a hir::ItemContext,
        body: &'a mir::Body,
        is_method: bool,
        viper_body: &'a mut ViperBody,
        source_map: &'a mut ViperSourceMap,
    ) -> Self {
        let cfg = cfg::Cfg::compute(body);
        Self {
            db,
            cx,
            body,
            is_method,
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

    pub fn lower_type(&mut self, ty: hir::Type) -> ViperType {
        match ty.data(self.db) {
            hir::TypeData::Error => {
                // TODO: Perhaps this should be handeld at a previous stage?
                VTy::int().into()
            }
            hir::TypeData::Void => {
                // TODO: Perhaps this should be handeld at a previous stage?
                // VTy::internal_type().into()
                VTy::int().into()
            }
            hir::TypeData::Ghost(inner) => {
                // TODO: Should we do anything special about ghost?
                self.lower_type(*inner)
            }
            &hir::TypeData::Ref { is_mut, inner } => {
                // TODO: We should indicate some predicate on the ref
                ViperType {
                    vty: VTy::ref_(),
                    is_mut,
                    optional: false,
                }
            }
            hir::TypeData::List(inner) => VTy::Seq {
                element_type: Box::new(self.lower_type(*inner).vty),
            }
            .into(),
            hir::TypeData::Optional(inner) => {
                let vty = self.lower_type(*inner);
                ViperType {
                    optional: true,
                    ..vty
                }
            }
            hir::TypeData::Primitive(p) => match p {
                hir::Primitive::Int => VTy::int().into(),
                hir::Primitive::Bool => VTy::bool().into(),
            },
            hir::TypeData::Struct(s) => match s.name(self.db).as_str() {
                "Multiset" => VTy::Multiset {
                    element_type: Box::new(VTy::int()),
                }
                .into(),
                _ => VTy::ref_().into(),
            },
            hir::TypeData::Null => todo!("lower_type(Null)"),
            hir::TypeData::Function { .. } => todo!("lower_type(Function)"),
            hir::TypeData::Range(inner) => VTy::Domain {
                domain_name: "Range".to_string(),
                partial_typ_vars_map: Default::default(),
            }
            .into(),
        }
    }

    fn can_inline(&self, x: mir::SlotId, exp: VExprId) -> bool {
        // TODO: This entire thing should be better specified
        // return false;
        let n = self.body.reference_to(x).count();
        match &*self.viper_body[exp] {
            _ if n < 2 && Some(x) != self.body.result_slot() => true,
            // Exp::Literal(_) => true,
            Exp::AbstractLocalVar(_) => {
                // TODO: We should be able inline these, as long as the
                // assignmed slot is immutable
                false
            }
            _ => false,
        }
    }
}

impl BodyLower<'_> {
    fn alloc(&mut self, source: impl Into<BlockOrInstruction>, vexpr: VExpr) -> VExprId {
        let item_id = self.body.item_id();
        let id = self.viper_body.arena.alloc(vexpr);
        match source.into() {
            BlockOrInstruction::Block(block_id) => {
                self.source_map.block_expr.insert((item_id, block_id), id);
                self.source_map
                    .block_expr_back
                    .insert(id, (item_id, block_id));
            }
            BlockOrInstruction::Instruction(inst_id) => {
                self.source_map.inst_expr.insert((item_id, inst_id), id);
                self.source_map
                    .inst_expr_back
                    .insert(id, (item_id, inst_id));
            }
        }
        id
    }
    fn function(
        &mut self,
        source: impl Into<BlockOrInstruction> + Copy,
        fid: mir::FunctionId,
        args: &[mir::Operand],
    ) -> Result<Exp<VExprId>, ViperLowerError> {
        Ok(match &*self.body[fid] {
            mir::FunctionData::Named(v) => Exp::new_func_app(
                self.cx.var_ident(*v).to_string(),
                args.iter()
                    .map(|s| self.operand_to_ref(source, s))
                    .collect(),
            ),
            mir::FunctionData::Index => {
                let base = self.operand_to_ref(source, &args[0]);
                let index = self.operand_to_ref(source, &args[1]);
                Exp::Seq(SeqExp::new_index(base, index))
            }
            mir::FunctionData::RangeIndex => {
                let base = self.operand_to_ref(source, &args[0]);
                let index = self.operand_to_ref(source, &args[1]);
                Exp::new_func_app("range_index".to_string(), vec![base, index])
            }
            mir::FunctionData::Range(op) => {
                let (f, args) = match op {
                    mir::RangeKind::FromTo => (
                        "range_from_to",
                        vec![
                            self.operand_to_ref(source, &args[0]),
                            self.operand_to_ref(source, &args[1]),
                        ],
                    ),
                    mir::RangeKind::From => {
                        ("range_from", vec![self.operand_to_ref(source, &args[0])])
                    }
                    mir::RangeKind::To => ("range_to", vec![self.operand_to_ref(source, &args[0])]),
                    mir::RangeKind::Full => ("range_full", vec![]),
                };
                Exp::new_func_app(f.to_string(), args)
            }
            mir::FunctionData::List => Exp::Seq(SeqExp::new_explicit(
                args.iter()
                    .map(|s| self.operand_to_ref(source, s))
                    .collect(),
            )),
        })
    }

    pub(super) fn slot_to_decl(&mut self, x: mir::SlotId) -> LocalVarDecl {
        let var = self.slot_to_var(x);
        LocalVarDecl::new(var.name, var.typ)
    }
    fn slot_to_var(&mut self, x: mir::SlotId) -> LocalVar {
        match &self.body[x] {
            mir::Slot::Var(var) => LocalVar::new(
                format!("{}_{}", self.cx.var_ident(*var), x.into_raw()),
                self.lower_type(self.body.slot_ty(x)).vty,
            ),
            _ => LocalVar::new(
                format!("_{}", x.into_raw()),
                self.lower_type(self.body.slot_ty(x)).vty,
            ),
        }
    }
    fn slot_to_ref(&mut self, source: impl Into<BlockOrInstruction>, s: mir::SlotId) -> VExprId {
        *self.times_referenced.entry(s).or_default() += 1;
        let var = self.slot_to_var(s);
        *self.var_refs.entry(s).or_insert_with(|| {
            let exp = match &self.body[s] {
                mir::Slot::Temp | mir::Slot::Var(_) => {
                    Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(var))
                }
                mir::Slot::Result => {
                    if self.is_method {
                        Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(var))
                    } else {
                        Exp::AbstractLocalVar(AbstractLocalVar::Result { typ: var.typ })
                    }
                }
            };

            let item_id = self.body.item_id();
            // TODO: This does not work since we are in a FnMut
            // self.alloc(source, VExpr::new(exp))
            let id = self.viper_body.arena.alloc(VExpr::new(exp));
            match source.into() {
                BlockOrInstruction::Block(block_id) => {
                    self.source_map.block_expr.insert((item_id, block_id), id);
                    self.source_map
                        .block_expr_back
                        .insert(id, (item_id, block_id));
                }
                BlockOrInstruction::Instruction(inst_id) => {
                    self.source_map.inst_expr.insert((item_id, inst_id), id);
                    self.source_map
                        .inst_expr_back
                        .insert(id, (item_id, inst_id));
                }
            }
            id
        })
    }
    fn operand_to_ref(
        &mut self,
        source: impl Into<BlockOrInstruction>,
        o: &mir::Operand,
    ) -> VExprId {
        match o {
            mir::Operand::Copy(s) => self.slot_to_ref(source, *s),
            mir::Operand::Move(s) => self.slot_to_ref(source, *s),
            mir::Operand::Literal(l) => {
                let exp = lower_lit(l);

                let item_id = self.body.item_id();
                // TODO: This does not work since we are in a FnMut
                // self.alloc(source, VExpr::new(exp))
                let id = self.viper_body.arena.alloc(VExpr::new(exp));
                match source.into() {
                    BlockOrInstruction::Block(block_id) => {
                        self.source_map.block_expr.insert((item_id, block_id), id);
                        self.source_map
                            .block_expr_back
                            .insert(id, (item_id, block_id));
                    }
                    BlockOrInstruction::Instruction(inst_id) => {
                        self.source_map.inst_expr.insert((item_id, inst_id), id);
                        self.source_map
                            .inst_expr_back
                            .insert(id, (item_id, inst_id));
                    }
                }
                id
            }
        }
    }

    fn expr(
        &mut self,
        inst: mir::InstructionId,
        e: &mir::MExpr,
    ) -> Result<VExprId, ViperLowerError> {
        let exp = match e {
            mir::MExpr::Field(rcr, f) => match &f.parent {
                hir::FieldParent::Struct(_) => {
                    return Err(ViperLowerError::NotYetImplemented {
                        msg: format!("lower struct field: {f:?}"),
                        item_id: self.body.item_id(),
                        block_or_inst: Some(inst.into()),
                        span: None,
                    });
                }
                hir::FieldParent::List(_) => match f.name.as_str() {
                    "len" => Exp::Seq(SeqExp::new_length(self.operand_to_ref(inst, rcr))),
                    _ => {
                        return Err(ViperLowerError::NotYetImplemented {
                            msg: format!("lower list field: {f:?}"),
                            item_id: self.body.item_id(),
                            block_or_inst: Some(inst.into()),
                            span: None,
                        });
                    }
                },
            },
            mir::MExpr::Struct(s, fields) => {
                Exp::FuncApp {
                    funcname: format!("init_{}", s.name(self.db)),
                    args: fields
                        .iter()
                        .map(|(_, s)| self.operand_to_ref(inst, s))
                        .collect(),
                }

                // return Err(ViperLowerError::NotYetImplemented(
                //     "lower struct".to_string(),
                // ));
            }
            mir::MExpr::Use(s) => {
                let item_id = self.body.item_id();
                let id = self.operand_to_ref(inst, s);
                self.source_map.inst_expr.insert((item_id, inst), id);
                self.source_map.inst_expr_back.insert(id, (item_id, inst));
                return Ok(id);
            }
            mir::MExpr::BinaryOp(op, l, r) => {
                let op = lower_binop(op).expect("assignment should have been filtered out by now");
                let lhs = self.operand_to_ref(inst, l);
                let rhs = self.operand_to_ref(inst, r);
                Exp::new_bin(op, lhs, rhs)
            }
            mir::MExpr::UnaryOp(op, x) => {
                use mist_syntax::ast::operators::UnaryOp;

                let op = match op {
                    UnaryOp::Not => UnOp::Not,
                    UnaryOp::Neg => UnOp::Minus,
                };
                let x = self.operand_to_ref(inst, x);
                Exp::new_un(op, x)
            }
        };
        Ok(self.alloc(inst, VExpr::new(exp)))
    }
}
