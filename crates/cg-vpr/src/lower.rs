mod folding;
pub mod method;
pub mod pure;
pub mod pure_next;
pub mod structs;

use std::{
    cmp::Ordering,
    collections::{HashMap, HashSet},
};

use derive_new::new;

use itertools::Either;
use miette::Diagnostic;
use mist_core::{
    hir,
    mir::{self, analysis::cfg},
    mono::{
        self,
        exprs::Field,
        types::{Adt, Type, TypeData},
    },
    types::{
        AdtKind, BuiltinField, BuiltinKind, ListField, MultiSetField, Primitive, RangeField,
        SetField,
    },
    util::{IdxArena, IdxMap, IdxWrap},
};
use mist_syntax::{
    ast::{
        operators::{ArithOp, BinaryOp, CmpOp, LogicOp},
        Spanned,
    },
    SourceSpan,
};
use silvers::{
    expression::{
        AbstractLocalVar, AccessPredicate, BinOp, Exp, FieldAccess, LocalVar, MultisetExp, PermExp,
        PredicateAccess, PredicateAccessPredicate, SeqExp, SetExp, UnOp,
    },
    program::{Field as VField, LocalVarDecl},
    typ::Type as VTy,
};
use tracing::error;

use crate::{
    gen::{VExpr, VExprId},
    mangle,
};

use self::folding::{q_ref_acc, q_ref_perm, q_ref_strip_value, q_ref_unfolding, q_ref_value};

fn lower_binop(op: BinaryOp) -> Option<BinOp> {
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

fn lower_lit(l: hir::Literal) -> Exp<VExprId> {
    match l {
        hir::Literal::Null => Exp::null(),
        hir::Literal::Int(i) => Exp::int(i),
        hir::Literal::Bool(b) => Exp::boolean(b),
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
        ib: &'a mir::ItemBody,
        is_method: bool,
    ) -> BodyLower<'a> {
        BodyLower::new(db, ib, is_method, &mut self.viper_body, &mut self.source_map)
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
    pub inst_expr: HashMap<(mono::Item, mir::InstructionId), VExprId>,
    pub inst_expr_back: IdxMap<VExprId, (mono::Item, mir::InstructionId)>,
    pub block_expr: HashMap<(mono::Item, mir::BlockId), VExprId>,
    pub block_expr_back: IdxMap<VExprId, (mono::Item, mir::BlockId)>,
}

impl ViperSourceMap {
    pub fn trace_exp(&self, exp: VExprId) -> Option<(mono::Item, mir::BlockOrInstruction)> {
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
        def: mono::Item,
        block_or_inst: Option<mir::BlockOrInstruction>,
        #[label]
        span: Option<SourceSpan>,
    },
    #[error("the body did not contain any actions")]
    EmptyBody,
}

impl ViperLowerError {
    pub fn populate_spans(&mut self, db: &dyn crate::Db) {
        let f = |item, block_or_instr| {
            let item_mir = mir::lower_item(db, item)?;
            let expr = item_mir.source_map(db).trace_expr(block_or_instr)?;
            Some(expr.ast(db).span())
        };

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
    pub adt: Option<Adt>,
}

impl From<VTy> for ViperType {
    fn from(vty: VTy) -> Self {
        ViperType { vty, is_mut: false, is_ref: false, optional: false, inner: None, adt: None }
    }
}

pub struct BodyLower<'a> {
    db: &'a dyn crate::Db,
    ib: &'a mir::ItemBody,
    viper_body: &'a mut ViperBody,
    source_map: &'a mut ViperSourceMap,
    is_method: bool,
    cfg: cfg::Cfg,
    postdominators: cfg::Postdominators,
    var_refs: IdxMap<mir::LocalId, VExprId>,
    current_source: Option<mir::BlockOrInstruction>,
    /// Places which are implicitly already unfolded.
    ///
    /// This is relevant in predicates for example, where fields are accessible
    /// without unfolding.
    pre_unfolded: HashSet<mir::Place>,
    inlined: IdxMap<VExprId, VExprId>,
    place_alias: HashMap<mir::Place, VExprId>,
    internally_bound_locals: IdxMap<mir::LocalId, ()>,
}

impl<'a> BodyLower<'a> {
    pub fn new(
        db: &'a dyn crate::Db,
        ib: &'a mir::ItemBody,
        is_method: bool,
        viper_body: &'a mut ViperBody,
        source_map: &'a mut ViperSourceMap,
    ) -> Self {
        let cfg = cfg::Cfg::compute(db, ib);
        Self {
            db,
            ib,
            is_method,
            viper_body,
            source_map,
            cfg,
            postdominators: Default::default(),
            var_refs: Default::default(),
            current_source: None,
            pre_unfolded: Default::default(),
            inlined: Default::default(),
            place_alias: Default::default(),
            internally_bound_locals: Default::default(),
        }
    }

    pub fn begin_scope<T>(
        &mut self,
        source: impl Into<mir::BlockOrInstruction>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let prev_src = self.current_source.replace(source.into());
        let prev = self.place_alias.clone();
        let res = f(self);
        self.place_alias = prev;
        self.current_source = prev_src;
        res
    }

    pub fn alias(&mut self, place: mir::Place, into: VExprId) {
        self.place_alias.insert(place, into);
    }

    pub fn lower_type(&mut self, ty: Type) -> Result<ViperType> {
        Ok(match ty.kind(self.db) {
            TypeData::Error => {
                error!(ty=?ty.display(self.db).to_string(), "lowered invalid type data");
                // TODO: Perhaps this should be handeld at a previous stage?
                VTy::int().into()
            }
            TypeData::Void => {
                error!(ty=?ty.display(self.db).to_string(), "lowered invalid type data");
                // TODO: Perhaps this should be handeld at a previous stage?
                // VTy::internal_type().into()
                VTy::int().into()
            }
            TypeData::Generic(_) => {
                error!(ty=?ty.display(self.db).to_string(), "lowered invalid type data");
                // TODO: Perhaps this should be handeld at a previous stage?
                // VTy::internal_type().into()
                VTy::int().into()
            }
            TypeData::Ref { is_mut, inner } => ViperType {
                vty: if is_mut {
                    VTy::ref_()
                } else {
                    VTy::Domain {
                        domain_name: "QRef".to_string(),
                        partial_typ_vars_map: Default::default(),
                    }
                },
                is_mut,
                is_ref: true,
                optional: false,
                inner: Some(Box::new(self.lower_type(inner)?)),
                adt: None,
            },
            TypeData::Optional(inner) => {
                let vty = self.lower_type(inner)?;
                ViperType { optional: true, ..vty }
            }
            TypeData::Primitive(p) => match p {
                Primitive::Int => VTy::int().into(),
                Primitive::Bool => VTy::bool().into(),
            },
            TypeData::Builtin(b) => {
                let gargs = b
                    .generic_args(self.db)
                    .iter()
                    .map(|t| Ok(self.lower_type(*t)?.vty))
                    .collect::<Result<Vec<_>>>()?;
                let arg = |idx| Box::new(gargs.get(idx).cloned().unwrap_or_else(VTy::int));
                match b.kind(self.db) {
                    BuiltinKind::Set => VTy::Set { element_type: arg(0) }.into(),
                    BuiltinKind::MultiSet => VTy::Multiset { element_type: arg(0) }.into(),
                    BuiltinKind::Map => VTy::Map { key_type: arg(0), value_type: arg(1) }.into(),
                    BuiltinKind::List => VTy::Seq { element_type: arg(0) }.into(),
                    BuiltinKind::Range => VTy::Domain {
                        domain_name: "Range".to_string(),
                        partial_typ_vars_map: Default::default(),
                    }
                    .into(),
                }
            }
            TypeData::Adt(adt) => match adt.kind(self.db) {
                AdtKind::Struct(_, _) if adt.is_pure(self.db) => ViperType {
                    vty: VTy::Domain {
                        domain_name: mangle::mangled_adt(self.db, adt),
                        partial_typ_vars_map: Default::default(),
                    },
                    optional: false,
                    is_mut: false,
                    is_ref: false,
                    inner: None,
                    adt: Some(adt),
                },
                AdtKind::Struct(_, _) => ViperType {
                    vty: VTy::ref_(),
                    optional: false,
                    is_mut: false,
                    is_ref: false,
                    inner: None,
                    adt: Some(adt),
                },
                AdtKind::Enum => todo!(),
            },
            TypeData::Null => ViperType {
                vty: VTy::ref_(),
                optional: true,
                is_mut: false,
                inner: None,
                is_ref: false,
                adt: None,
            },
            TypeData::Function { .. } => {
                return Err(ViperLowerError::NotYetImplemented {
                    msg: "lower_type(Function)".to_string(),
                    def: self.ib.item(),
                    block_or_inst: None,
                    span: None,
                })
            }
        })
    }

    fn can_inline(&self, x: mir::Place, exp: VExprId) -> bool {
        // TODO: This entire thing should be better specified
        // return false;
        let n = self.ib.reference_to(self.db, x.local()).count();
        match &*self.viper_body[exp] {
            _ if n < 2 && !x.local().is_result(self.ib) => true,
            // Exp::Literal(_) => true,
            Exp::AbstractLocalVar(_) => {
                // TODO: We should be able inline these, as long as the
                // assignmed local is immutable
                false
            }
            _ => false,
        }
    }
}

impl BodyLower<'_> {
    pub(crate) fn alloc(
        &mut self,
        source: impl Into<mir::BlockOrInstruction>,
        vexpr: impl Into<Exp<VExprId>>,
    ) -> VExprId {
        let item_id = self.ib.item();
        let id = self.viper_body.arena.alloc(VExpr::new(vexpr.into()));
        match source.into() {
            mir::BlockOrInstruction::Block(block_id) => {
                self.source_map.block_expr.insert((item_id, block_id), id);
                self.source_map.block_expr_back.insert(id, (item_id, block_id));
            }
            mir::BlockOrInstruction::Instruction(inst_id) => {
                self.source_map.inst_expr.insert((item_id, inst_id), id);
                self.source_map.inst_expr_back.insert(id, (item_id, inst_id));
            }
        }
        id
    }
    pub(crate) fn allocs(&mut self, vexpr: impl Into<Exp<VExprId>>) -> VExprId {
        self.alloc(self.current_source.expect("no source was set"), vexpr)
    }
    fn function(&mut self, f: mir::Function, args: &[mir::Operand]) -> Result<Exp<VExprId>> {
        Ok(match f {
            mir::Function::Named(v) => Exp::new_func_app(
                v.name(self.db).to_string(),
                args.iter().map(|&s| self.operand_to_ref(s)).collect::<Result<_>>()?,
            ),
            mir::Function::BuiltinMethod(bf) => match bf {
                BuiltinField::List(_, lf) => match lf {
                    ListField::Len => todo!(),
                    ListField::ToSet => {
                        let list = self.operand_to_ref(args[0])?;
                        Exp::new_func_app("list_to_set".to_string(), vec![list])
                    }
                    ListField::ToMultiSet => {
                        let list = self.operand_to_ref(args[0])?;
                        Exp::new_func_app("list_to_multi_set".to_string(), vec![list])
                    }
                },
                BuiltinField::Set(_, sf) => match sf {
                    SetField::Cardinality => todo!(),
                    SetField::Contains => {
                        let set = self.operand_to_ref(args[0])?;
                        let element = self.operand_to_ref(args[1])?;
                        Exp::new_set(SetExp::Bin {
                            op: silvers::expression::SetBinOp::Contains,
                            left: element,
                            right: set,
                        })
                    }
                    SetField::Union => {
                        let a = self.operand_to_ref(args[0])?;
                        let b = self.operand_to_ref(args[1])?;
                        Exp::new_set(SetExp::Bin {
                            op: silvers::expression::SetBinOp::Union,
                            left: a,
                            right: b,
                        })
                    }
                    SetField::Intersection => {
                        let a = self.operand_to_ref(args[0])?;
                        let b = self.operand_to_ref(args[1])?;
                        Exp::new_set(SetExp::Bin {
                            op: silvers::expression::SetBinOp::Intersection,
                            left: a,
                            right: b,
                        })
                    }
                    SetField::ToList => {
                        let set = self.operand_to_ref(args[0])?;
                        Exp::new_func_app("set_to_list".to_string(), vec![set])
                    }
                },
                BuiltinField::MultiSet(_, mf) => match mf {
                    MultiSetField::Cardinality => todo!(),
                    MultiSetField::ToList => {
                        let set = self.operand_to_ref(args[0])?;
                        Exp::new_func_app("multi_set_to_list".to_string(), vec![set])
                    }
                },
                BuiltinField::Range(_, _) => todo!(),
            },
            mir::Function::Index => {
                let base = self.operand_to_ref(args[0])?;
                let index = self.operand_to_ref(args[1])?;
                SeqExp::new_index(base, index).into()
            }
            mir::Function::RangeIndex => {
                let base = self.operand_to_ref(args[0])?;
                let index = self.operand_to_ref(args[1])?;
                Exp::new_func_app("range_index".to_string(), vec![base, index])
            }
            mir::Function::Range(op) => {
                let (f, args) = match op {
                    mir::RangeKind::FromTo => (
                        "range_from_to",
                        vec![self.operand_to_ref(args[0])?, self.operand_to_ref(args[1])?],
                    ),
                    mir::RangeKind::From => ("range_from", vec![self.operand_to_ref(args[0])?]),
                    mir::RangeKind::To => ("range_to", vec![self.operand_to_ref(args[0])?]),
                    mir::RangeKind::Full => ("range_full", vec![]),
                };
                Exp::new_func_app(f.to_string(), args)
            }
            mir::Function::List => SeqExp::new_explicit(
                args.iter().map(|&s| self.operand_to_ref(s)).collect::<Result<_>>()?,
            )
            .into(),
            mir::Function::ListConcat => {
                SeqExp::new_append(self.operand_to_ref(args[0])?, self.operand_to_ref(args[1])?)
                    .into()
            }
            mir::Function::InRange => {
                let idx = self.operand_to_ref(args[0])?;
                let r = self.operand_to_ref(args[1])?;
                Exp::new_func_app("in_range".to_string(), vec![idx, r])
            }
            mir::Function::RangeMin => {
                let r = self.operand_to_ref(args[0])?;
                Exp::new_func_app("range_min".to_string(), vec![r])
            }
            mir::Function::RangeMax => {
                let r = self.operand_to_ref(args[0])?;
                Exp::new_func_app("range_max".to_string(), vec![r])
            }
        })
    }

    pub(super) fn local_to_decl(&mut self, x: mir::LocalId) -> Result<LocalVarDecl> {
        let var = self.local_to_var(x)?;
        Ok(LocalVarDecl::new(var.name, var.typ))
    }
    pub(super) fn local_to_var(&mut self, x: mir::LocalId) -> Result<LocalVar> {
        Ok(match x.data(self.ib) {
            mir::Local::Variable(var) => LocalVar::new(
                format!("{}_{}", var.name(self.db), x.into_raw()),
                self.lower_type(x.ty(self.db, self.ib))?.vty,
            ),
            _ => LocalVar::new(
                format!("_{}", x.into_raw()),
                self.lower_type(x.ty(self.db, self.ib))?.vty,
            ),
        })
    }
    pub(super) fn place_to_ref(&mut self, p: mir::Place) -> Result<VExprId> {
        if let Some(alias) = self.place_alias.get(&p).copied() {
            return Ok(alias);
        }

        let var = self.local_to_var(p.local())?;
        if !p.has_projection(self.db) {
            if let Some(exp) = self.var_refs.get(p.local()).copied() {
                return Ok(exp);
            }
        }

        let id = match p.local().data(self.ib) {
            mir::Local::Temp
            | mir::Local::Self_
            | mir::Local::Param(_)
            | mir::Local::Quantified(_)
            | mir::Local::Variable(_) => {
                let exp = self.allocs(AbstractLocalVar::LocalVar(var));
                if p.local().ty(self.db, self.ib).is_shared_ref(self.db) {
                    q_ref_value(self, exp)
                } else {
                    exp
                }
            }
            mir::Local::Result => self.allocs(if self.is_method {
                AbstractLocalVar::LocalVar(var)
            } else {
                AbstractLocalVar::Result { typ: var.typ }
            }),
        };

        self.var_refs.insert(p.local(), id);

        p.projection_iter(self.db).try_fold(id, |base, proj| -> Result<_> {
            Ok(match proj {
                mir::Projection::Field(f) => {
                    match f {
                        Field::Builtin(bf, _) => match bf {
                            BuiltinField::List(_, ListField::Len) => {
                                let exp = SeqExp::Length { s: base };
                                self.allocs(exp)
                            }
                            BuiltinField::List(_, ListField::ToSet | ListField::ToMultiSet) => {
                                unreachable!()
                            }
                            BuiltinField::Set(_, SetField::Cardinality) => {
                                let exp = SetExp::Cardinality { s: base };
                                self.allocs(exp)
                            }
                            BuiltinField::Set(
                                _,
                                SetField::Contains
                                | SetField::Union
                                | SetField::Intersection
                                | SetField::ToList,
                            ) => {
                                unreachable!()
                            }
                            BuiltinField::MultiSet(_, MultiSetField::Cardinality) => {
                                let exp = MultisetExp::Cardinality { s: base };
                                self.allocs(exp)
                            }
                            BuiltinField::MultiSet(_, MultiSetField::ToList) => {
                                unreachable!()
                            }
                            BuiltinField::Range(_, rf) => match rf {
                                RangeField::Min => {
                                    let exp =
                                        Exp::new_func_app("range_min".to_string(), vec![base]);
                                    self.allocs(exp)
                                }
                                RangeField::Max => {
                                    let exp =
                                        Exp::new_func_app("range_max".to_string(), vec![base]);
                                    self.allocs(exp)
                                }
                            },
                        },
                        Field::AdtField(adt, af) => {
                            let exp = if adt.is_pure(self.db) {
                                Exp::FuncApp {
                                    funcname: mangle::mangled_adt_field(self.db, adt, af),
                                    args: vec![base],
                                }
                            } else {
                                VField::new(
                                    mangle::mangled_adt_field(self.db, adt, af),
                                    // TODO: Should we look at the contraints?
                                    self.lower_type(af.ty(self.db))?.vty,
                                )
                                .access_exp(base)
                            };
                            self.allocs(exp)
                        }
                        Field::Undefined => todo!(),
                    }
                }
                mir::Projection::Index(index, _) => {
                    let idx = self.local_to_var(index)?;
                    let idx = self.allocs(AbstractLocalVar::LocalVar(idx));
                    self.allocs(SeqExp::Index { s: base, idx })
                }
            })
        })
    }
    fn operand_to_ref(&mut self, o: mir::Operand) -> Result<VExprId> {
        Ok(match o {
            mir::Operand::Copy(s) => self.place_to_ref(s)?,
            mir::Operand::Move(s) => self.place_to_ref(s)?,
            mir::Operand::Literal(l) => self.allocs(lower_lit(l)),
        })
    }
    fn place_for_assignment(&mut self, dest: mir::Place) -> Result<LocalVar> {
        if !dest.has_projection(self.db) {
            self.local_to_var(dest.local())
        } else {
            todo!()
        }
    }

    fn expr(&mut self, inst: mir::InstructionId, e: &mir::MExpr) -> Result<VExprId> {
        let exp = match e {
            &mir::MExpr::Use(s) => {
                let item_id = self.ib.item();
                let id = self.operand_to_ref(s)?;
                self.source_map.inst_expr.insert((item_id, inst), id);
                self.source_map.inst_expr_back.insert(id, (item_id, inst));
                return Ok(id);
            }
            mir::MExpr::Ref(bk, p) => {
                // TODO: Perhaps we should do something different depending on this?
                let _ = bk;

                let item_id = self.ib.item();
                let id = self.place_to_ref(*p)?;
                self.source_map.inst_expr.insert((item_id, inst), id);
                self.source_map.inst_expr_back.insert(id, (item_id, inst));
                return Ok(id);
            }
            &mir::MExpr::BinaryOp(op, l, r) => {
                let op = lower_binop(op).expect("assignment should have been filtered out by now");
                let lhs = self.operand_to_ref(l)?;
                let rhs = self.operand_to_ref(r)?;
                Exp::new_bin(op, lhs, rhs)
            }
            &mir::MExpr::UnaryOp(op, x) => {
                use mist_syntax::ast::operators::UnaryOp;

                let x = self.operand_to_ref(x)?;

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
        Ok(self.allocs(exp))
    }

    pub(super) fn ty_to_condition(
        &mut self,
        place: VExprId,
        ty: Type,
    ) -> Result<(Option<VExprId>, Option<VExprId>)> {
        let vty = self.lower_type(ty)?;
        match vty.adt {
            Some(adt) if !adt.is_pure(self.db) => {
                let perm = self.allocs(PermExp::Full);
                let pred = self.allocs(AccessPredicate::Predicate(PredicateAccessPredicate::new(
                    PredicateAccess::new(mangle::mangled_adt(self.db, adt), vec![place]),
                    perm,
                )));
                let pred = if vty.optional {
                    let null = self.allocs(Exp::null());
                    let cond = self.allocs(Exp::bin(place, BinOp::NeCmp, null));
                    self.allocs(Exp::bin(cond, BinOp::Implies, pred))
                } else {
                    pred
                };
                return Ok((Some(pred), None));
            }
            _ => (),
        }
        if let Some(inner) = vty.inner {
            if vty.is_ref {
                if let Some(st) = inner.adt {
                    let (exp, end_exp) = if vty.is_mut {
                        let perm = self.allocs(PermExp::Full);
                        let exp =
                            self.allocs(AccessPredicate::Predicate(PredicateAccessPredicate::new(
                                PredicateAccess::new(mangle::mangled_adt(self.db, st), vec![place]),
                                perm,
                            )));
                        (exp, exp)
                    } else {
                        let full = self.allocs(PermExp::Full);
                        let place = q_ref_strip_value(self, place);
                        let exp = q_ref_acc(self.db, self, st, place, full);
                        let cur_perm = q_ref_perm(self, place);
                        let none = self.allocs(PermExp::No);
                        let positive_perm = self.allocs(Exp::bin(cur_perm, BinOp::GtCmp, none));
                        let no_write_perm = self.allocs(Exp::bin(full, BinOp::GtCmp, cur_perm));
                        let perm_bound_exp =
                            self.allocs(Exp::bin(no_write_perm, BinOp::And, positive_perm));
                        let exp = self.allocs(Exp::bin(exp, BinOp::And, perm_bound_exp));

                        let place_value = q_ref_value(self, place);
                        let end_exp = st.fields(self.db).iter().fold(exp, |acc, f| {
                            let field = self.allocs(Exp::LocationAccess(
                                silvers::expression::ResourceAccess::Location(
                                    silvers::expression::LocationAccess::Field(FieldAccess {
                                        rcr: place_value,
                                        field: VField {
                                            name: mangle::mangled_adt_field(self.db, st, *f),
                                            typ: VTy::internal_type(),
                                        },
                                    }),
                                ),
                            ));
                            let field = q_ref_unfolding(self.db, self, st, place, full, field);
                            let old_field = self
                                .allocs(Exp::Old(silvers::expression::OldExp::Old { exp: field }));
                            let field_eq_old_field =
                                self.allocs(Exp::bin(field, BinOp::EqCmp, old_field));

                            self.allocs(Exp::bin(acc, BinOp::And, field_eq_old_field))
                        });

                        (exp, end_exp)

                        // self.allocs(AccessPredicate::Predicate(PredicateAccessPredicate::new(
                        //     PredicateAccess::new(mangle::mangled_adt(self.db, st), vec![place]),
                        //     perm,
                        // )))
                    };
                    return Ok((Some(exp), Some(end_exp)));
                }
            }
        }
        Ok((None, None))
    }
}
