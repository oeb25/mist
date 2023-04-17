use std::{cmp::Ordering, io::Write, process::Stdio};

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

#[derive(Debug, Default)]
pub struct ViperBody {
    arena: Arena<VExpr>,
}

impl std::ops::Index<VExprId> for ViperBody {
    type Output = VExpr;

    fn index(&self, index: VExprId) -> &Self::Output {
        &self.arena[index]
    }
}

#[derive(Debug, Default)]
pub struct ViperSourceMap {
    inst_expr: ArenaMap<mir::InstructionId, VExprId>,
    inst_expr_back: ArenaMap<VExprId, mir::InstructionId>,
}

#[derive(Debug, Clone, thiserror::Error, Diagnostic)]
pub enum ViperLowerError {
    #[error("not yet implemented: {_0}")]
    NotYetImplemented(String),
    #[error("the body did not contain any actions")]
    EmptyBody,
}

#[salsa::accumulator]
pub struct ViperLowerErrors(ViperLowerError);
