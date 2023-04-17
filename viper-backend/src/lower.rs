use std::cmp::Ordering;

use derive_new::new;
use la_arena::{Arena, ArenaMap, Idx};

use miette::Diagnostic;
use mist_core::{
    hir,
    mir::{self, SlotId},
};
use mist_syntax::ast::operators::{ArithOp, BinaryOp, CmpOp, LogicOp};
use silvers::{
    expression::{AbstractLocalVar, BinOp, Exp, LocalVar, SeqExp, UnOp},
    program::LocalVarDecl,
    typ::Type as VTy,
};
use tracing::error;

use crate::gen::{VExpr, VExprId};

use self::pure::PureLower;

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
    pub fn pure<'a>(&'a mut self, cx: &'a hir::ItemContext, mir: &'a mir::Body) -> PureLower<'a> {
        PureLower::new(cx, mir, &mut self.viper_body, &mut self.source_map)
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
    inst_expr: ArenaMap<mir::InstructionId, VExprId>,
    inst_expr_back: ArenaMap<VExprId, mir::InstructionId>,
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error, Diagnostic)]
pub enum ViperLowerError {
    #[error("not yet implemented: {_0}")]
    NotYetImplemented(String),
    #[error("the body did not contain any actions")]
    EmptyBody,
}

#[salsa::accumulator]
pub struct ViperLowerErrors(ViperLowerError);
