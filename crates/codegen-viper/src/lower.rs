use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
};

use derive_new::new;

use itertools::Either;
use miette::Diagnostic;
use mist_core::{
    def, hir,
    mir::{self, analysis::cfg, BlockOrInstruction},
    types::{Field, ListField, Primitive, TypeProvider, TypePtr, TDK},
    util::{IdxArena, IdxMap, IdxWrap},
};
use mist_syntax::{
    ast::operators::{ArithOp, BinaryOp, CmpOp, LogicOp},
    SourceSpan,
};
use silvers::{
    expression::{
        AbstractLocalVar, AccessPredicate, BinOp, Exp, LocalVar, PermExp, PredicateAccess,
        PredicateAccessPredicate, SeqExp, UnOp,
    },
    program::{Field as VField, LocalVarDecl},
    typ::Type as VTy,
};
use tracing::error;

use crate::{
    gen::{VExpr, VExprId},
    mangle,
};

pub mod method;
pub mod pure;
pub mod structs;

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
        BodyLower::new(db, cx, mir, is_method, &mut self.viper_body, &mut self.source_map)
    }
    pub fn finish(self) -> (ViperBody, ViperSourceMap) {
        (self.viper_body, self.source_map)
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ViperBody {
    arena: IdxArena<VExprId>,
}

impl std::ops::Index<VExprId> for ViperBody {
    type Output = VExpr;

    fn index(&self, index: VExprId) -> &Self::Output {
        &self.arena[index]
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ViperSourceMap {
    pub inst_expr: HashMap<(def::Def, mir::InstructionId), VExprId>,
    pub inst_expr_back: IdxMap<VExprId, (def::Def, mir::InstructionId)>,
    pub block_expr: HashMap<(def::Def, mir::BlockId), VExprId>,
    pub block_expr_back: IdxMap<VExprId, (def::Def, mir::BlockId)>,
}

impl ViperSourceMap {
    pub fn trace_exp(&self, exp: VExprId) -> Option<(def::Def, mir::BlockOrInstruction)> {
        if let Some(&(item_id, instr)) = self.inst_expr_back.get(exp) {
            return Some((item_id, instr.into()));
        }
        if let Some(&(item_id, block)) = self.block_expr_back.get(exp) {
            return Some((item_id, block.into()));
        }
        None
    }
}

type Result<T> = std::result::Result<T, ViperLowerError>;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error, Diagnostic)]
pub enum ViperLowerError {
    #[error("not yet implemented: {msg}")]
    NotYetImplemented {
        msg: String,
        def: def::Def,
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
        f: impl Fn(def::Def, mir::BlockOrInstruction) -> Option<SourceSpan>,
    ) {
        match self {
            ViperLowerError::NotYetImplemented {
                def: item_id,
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
    pub optional: bool,
    pub is_mut: bool,
    pub inner: Option<Box<ViperType>>,
    pub is_ref: bool,
    pub strukt: Option<def::Struct>,
}

impl From<VTy> for ViperType {
    fn from(vty: VTy) -> Self {
        ViperType { vty, is_mut: false, is_ref: false, optional: false, inner: None, strukt: None }
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
    postdominators: cfg::Postdominators,
    var_refs: IdxMap<mir::SlotId, VExprId>,
    /// Places which are implicitly already unfolded.
    ///
    /// This is relevant in predicates for example, where fields are accessible
    /// without unfolding.
    pre_unfolded: HashSet<mir::Place>,
    inlined: IdxMap<VExprId, VExprId>,
    internally_bound_slots: IdxMap<mir::SlotId, ()>,
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
            postdominators: Default::default(),
            var_refs: Default::default(),
            pre_unfolded: Default::default(),
            inlined: Default::default(),
            internally_bound_slots: Default::default(),
        }
    }

    pub fn lower_type(&mut self, ty: TypePtr<impl TypeProvider>) -> Result<ViperType> {
        Ok(match ty.kind() {
            TDK::Error => {
                // TODO: Perhaps this should be handeld at a previous stage?
                VTy::int().into()
            }
            TDK::Void => {
                // TODO: Perhaps this should be handeld at a previous stage?
                // VTy::internal_type().into()
                VTy::int().into()
            }
            TDK::Free => {
                // TODO: Perhaps this should be handeld at a previous stage?
                // VTy::internal_type().into()
                VTy::int().into()
            }
            TDK::Ref { is_mut, inner } => ViperType {
                vty: VTy::ref_(),
                is_mut,
                is_ref: true,
                optional: false,
                inner: Some(Box::new(self.lower_type(inner)?)),
                strukt: None,
            },
            TDK::List(inner) => {
                VTy::Seq { element_type: Box::new(self.lower_type(inner)?.vty) }.into()
            }
            TDK::Optional(inner) => {
                let vty = self.lower_type(inner)?;
                ViperType { optional: true, ..vty }
            }
            TDK::Primitive(p) => match p {
                Primitive::Int => VTy::int().into(),
                Primitive::Bool => VTy::bool().into(),
            },
            TDK::Struct(s) => match s.name(self.db).as_str() {
                "Multiset" => VTy::Multiset { element_type: Box::new(VTy::int()) }.into(),
                _ => ViperType {
                    vty: VTy::ref_(),
                    optional: false,
                    is_mut: false,
                    is_ref: false,
                    inner: None,
                    strukt: Some(s),
                },
            },
            TDK::Null => ViperType {
                vty: VTy::ref_(),
                optional: true,
                is_mut: false,
                inner: None,
                is_ref: false,
                strukt: None,
            },
            TDK::Function { .. } => {
                return Err(ViperLowerError::NotYetImplemented {
                    msg: "lower_type(Function)".to_string(),
                    def: self.body.def(),
                    block_or_inst: None,
                    span: None,
                })
            }
            TDK::Range(_inner) => VTy::Domain {
                domain_name: "Range".to_string(),
                partial_typ_vars_map: Default::default(),
            }
            .into(),
        })
    }

    fn can_inline(&self, x: mir::Place, exp: VExprId) -> bool {
        // TODO: This entire thing should be better specified
        // return false;
        let n = self.body.reference_to(x.slot).count();
        match &*self.viper_body[exp] {
            _ if n < 2 && Some(x.slot) != self.body.result_slot() => true,
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
    pub(crate) fn alloc(
        &mut self,
        source: impl Into<BlockOrInstruction>,
        vexpr: impl Into<Exp<VExprId>>,
    ) -> VExprId {
        let item_id = self.body.def();
        let id = self.viper_body.arena.alloc(VExpr::new(vexpr.into()));
        match source.into() {
            BlockOrInstruction::Block(block_id) => {
                self.source_map.block_expr.insert((item_id, block_id), id);
                self.source_map.block_expr_back.insert(id, (item_id, block_id));
            }
            BlockOrInstruction::Instruction(inst_id) => {
                self.source_map.inst_expr.insert((item_id, inst_id), id);
                self.source_map.inst_expr_back.insert(id, (item_id, inst_id));
            }
        }
        id
    }
    fn function(
        &mut self,
        source: impl Into<BlockOrInstruction> + Copy,
        fid: mir::FunctionId,
        args: &[mir::Operand],
    ) -> Result<Exp<VExprId>> {
        Ok(match &*self.body[fid] {
            mir::FunctionData::Named(v) => Exp::new_func_app(
                self.cx.var_name(*v).to_string(),
                args.iter().map(|s| self.operand_to_ref(source, s)).collect::<Result<_>>()?,
            ),
            mir::FunctionData::Index => {
                let base = self.operand_to_ref(source, &args[0])?;
                let index = self.operand_to_ref(source, &args[1])?;
                SeqExp::new_index(base, index).into()
            }
            mir::FunctionData::RangeIndex => {
                let base = self.operand_to_ref(source, &args[0])?;
                let index = self.operand_to_ref(source, &args[1])?;
                Exp::new_func_app("range_index".to_string(), vec![base, index])
            }
            mir::FunctionData::Range(op) => {
                let (f, args) = match op {
                    mir::RangeKind::FromTo => (
                        "range_from_to",
                        vec![
                            self.operand_to_ref(source, &args[0])?,
                            self.operand_to_ref(source, &args[1])?,
                        ],
                    ),
                    mir::RangeKind::From => {
                        ("range_from", vec![self.operand_to_ref(source, &args[0])?])
                    }
                    mir::RangeKind::To => {
                        ("range_to", vec![self.operand_to_ref(source, &args[0])?])
                    }
                    mir::RangeKind::Full => ("range_full", vec![]),
                };
                Exp::new_func_app(f.to_string(), args)
            }
            mir::FunctionData::List => SeqExp::new_explicit(
                args.iter().map(|s| self.operand_to_ref(source, s)).collect::<Result<_>>()?,
            )
            .into(),
            mir::FunctionData::ListConcat => SeqExp::new_append(
                self.operand_to_ref(source, &args[0])?,
                self.operand_to_ref(source, &args[1])?,
            )
            .into(),
            mir::FunctionData::InRange => {
                let idx = self.operand_to_ref(source, &args[0])?;
                let r = self.operand_to_ref(source, &args[1])?;
                Exp::new_func_app("in_range".to_string(), vec![idx, r])
            }
            mir::FunctionData::RangeMin => {
                let r = self.operand_to_ref(source, &args[0])?;
                Exp::new_func_app("range_min".to_string(), vec![r])
            }
            mir::FunctionData::RangeMax => {
                let r = self.operand_to_ref(source, &args[0])?;
                Exp::new_func_app("range_max".to_string(), vec![r])
            }
        })
    }

    pub(super) fn slot_to_decl(&mut self, x: mir::SlotId) -> Result<LocalVarDecl> {
        let var = self.slot_to_var(x)?;
        Ok(LocalVarDecl::new(var.name, var.typ))
    }
    pub(super) fn slot_to_var(&mut self, x: mir::SlotId) -> Result<LocalVar> {
        Ok(match &self.body[x] {
            mir::Slot::Local(var) => LocalVar::new(
                format!("{}_{}", self.cx.var_name(*var), x.into_raw()),
                self.lower_type(self.body.slot_ty(x))?.vty,
            ),
            _ => LocalVar::new(
                format!("_{}", x.into_raw()),
                self.lower_type(self.body.slot_ty(x))?.vty,
            ),
        })
    }
    pub(super) fn place_to_ref(
        &mut self,
        source: impl Into<BlockOrInstruction> + Copy,
        p: mir::Place,
    ) -> Result<VExprId> {
        let var = self.slot_to_var(p.slot)?;
        if self.body[p.projection].is_empty() {
            if let Some(exp) = self.var_refs.get(p.slot).copied() {
                return Ok(exp);
            }
        }

        let exp = match &self.body[p.slot] {
            mir::Slot::Temp
            | mir::Slot::Self_
            | mir::Slot::Param(_)
            | mir::Slot::Quantified(_)
            | mir::Slot::Local(_) => AbstractLocalVar::LocalVar(var),
            mir::Slot::Result => {
                if self.is_method {
                    AbstractLocalVar::LocalVar(var)
                } else {
                    AbstractLocalVar::Result { typ: var.typ }
                }
            }
        };

        let id = self.alloc(source, exp);
        self.var_refs.insert(p.slot, id);

        self.body[p.projection].iter().copied().try_fold(id, |base, proj| -> Result<_> {
            Ok(match proj {
                mir::Projection::Field(f, ty) => {
                    match f {
                        Field::List(_, ListField::Len) => {
                            let exp = SeqExp::Length { s: base };
                            self.alloc(source, exp)
                        }
                        Field::StructField(sf) => {
                            let exp = VField::new(
                                mangle::mangled_field(self.db, sf),
                                // TODO: Should we look at the contraints?
                                self.lower_type(self.body.ty_ptr(ty))?.vty,
                            )
                            .access_exp(base);
                            self.alloc(source, exp)
                        }
                        Field::Undefined => todo!(),
                    }
                }
                mir::Projection::Index(index, _) => {
                    let idx = self.slot_to_var(index)?;
                    let idx = self.alloc(source, AbstractLocalVar::LocalVar(idx));
                    self.alloc(source, SeqExp::Index { s: base, idx })
                }
            })
        })
    }
    fn operand_to_ref(
        &mut self,
        source: impl Into<BlockOrInstruction> + Copy,
        o: &mir::Operand,
    ) -> Result<VExprId> {
        Ok(match o {
            mir::Operand::Copy(s) => self.place_to_ref(source, *s)?,
            mir::Operand::Move(s) => self.place_to_ref(source, *s)?,
            mir::Operand::Literal(l) => self.alloc(source, lower_lit(l)),
        })
    }
    fn place_for_assignment(&mut self, dest: mir::Place) -> Result<LocalVar> {
        if self.body[dest.projection].is_empty() {
            self.slot_to_var(dest.slot)
        } else {
            todo!()
        }
    }

    fn expr(&mut self, inst: mir::InstructionId, e: &mir::MExpr) -> Result<VExprId> {
        let exp = match e {
            mir::MExpr::Struct(s, fields) => {
                Exp::FuncApp {
                    funcname: format!("init_{}", s.name(self.db)),
                    args: fields
                        .iter()
                        .map(|(_, s)| self.operand_to_ref(inst, s))
                        .collect::<Result<_>>()?,
                }

                // return Err(ViperLowerError::NotYetImplemented(
                //     "lower struct".to_string(),
                // ));
            }
            mir::MExpr::Use(s) => {
                let item_id = self.body.def();
                let id = self.operand_to_ref(inst, s)?;
                self.source_map.inst_expr.insert((item_id, inst), id);
                self.source_map.inst_expr_back.insert(id, (item_id, inst));
                return Ok(id);
            }
            mir::MExpr::Ref(bk, p) => {
                // TODO: Perhaps we should do something different depending on this?
                let _ = bk;

                let item_id = self.body.def();
                let id = self.place_to_ref(inst, *p)?;
                self.source_map.inst_expr.insert((item_id, inst), id);
                self.source_map.inst_expr_back.insert(id, (item_id, inst));
                return Ok(id);
            }
            mir::MExpr::BinaryOp(op, l, r) => {
                let op = lower_binop(op).expect("assignment should have been filtered out by now");
                let lhs = self.operand_to_ref(inst, l)?;
                let rhs = self.operand_to_ref(inst, r)?;
                Exp::new_bin(op, lhs, rhs)
            }
            mir::MExpr::UnaryOp(op, x) => {
                use mist_syntax::ast::operators::UnaryOp;

                let x = self.operand_to_ref(inst, x)?;

                let op = match op {
                    UnaryOp::Not => Either::Left(UnOp::Not),
                    UnaryOp::Neg => Either::Left(UnOp::Minus),
                    UnaryOp::RangeMin => Either::Right("range_min".to_string()),
                    UnaryOp::RangeMax => Either::Right("range_max".to_string()),
                };
                match op {
                    Either::Left(op) => Exp::new_un(op, x),
                    Either::Right(funcname) => Exp::new_func_app(funcname, vec![x]),
                }
            }
        };
        Ok(self.alloc(inst, exp))
    }

    pub(super) fn ty_to_condition(
        &mut self,
        source: impl Into<BlockOrInstruction> + Copy,
        place: VExprId,
        ty: TypePtr<impl TypeProvider>,
    ) -> Result<(Option<VExprId>, Option<VExprId>)> {
        let ty = self.lower_type(ty)?;
        if let Some(st) = ty.strukt {
            let perm = self.alloc(source, PermExp::Full);
            let pred = self.alloc(
                source,
                AccessPredicate::Predicate(PredicateAccessPredicate::new(
                    PredicateAccess::new(mangle::mangled_struct(self.db, st), vec![place]),
                    perm,
                )),
            );
            let pred = if ty.optional {
                let null = self.alloc(source, Exp::null());
                let cond = self.alloc(source, Exp::bin(place, BinOp::NeCmp, null));
                self.alloc(source, Exp::bin(cond, BinOp::Implies, pred))
            } else {
                pred
            };
            return Ok((Some(pred), None));
        }
        if let Some(inner) = ty.inner {
            if ty.is_ref {
                if let Some(st) = inner.strukt {
                    let perm = if ty.is_mut {
                        self.alloc(source, PermExp::Full)
                    } else {
                        self.alloc(source, PermExp::Wildcard)
                    };
                    let exp = self.alloc(
                        source,
                        AccessPredicate::Predicate(PredicateAccessPredicate::new(
                            PredicateAccess::new(mangle::mangled_struct(self.db, st), vec![place]),
                            perm,
                        )),
                    );
                    return Ok((Some(exp), Some(exp)));
                }
            }
        }
        Ok((None, None))
    }
}
