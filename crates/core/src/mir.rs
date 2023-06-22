pub mod analysis;
pub mod def;
pub mod pass;
pub mod serialize;

use miette::Diagnostic;
use mist_syntax::SourceSpan;

use crate::mono::exprs::{ExprPtr, VariablePtr};

pub use def::{
    lower::lower_item,
    place::{Place, Projection, ProjectionList, Slot, SlotId},
    source_map::BodySourceMap,
    Action, Block, BlockId, BlockLocation, BlockOrInstruction, Body, BodyLocation, BorrowKind,
    Folding, Function, InBlock, Instruction, InstructionId, ItemBody, MExpr, Operand, RangeKind,
    SwitchTargets, Terminator, TerminatorKind,
};

#[salsa::tracked]
pub struct ItemMir {
    #[return_ref]
    pub ib: ItemBody,
    #[return_ref]
    pub source_map: BodySourceMap,
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error, Diagnostic)]
pub enum MirError {
    #[error("not yet implemented: {msg}")]
    NotYetImplemented {
        msg: String,
        expr: ExprPtr,
        #[label]
        span: Option<SourceSpan>,
    },
    #[error("variable used before its slot was allocated")]
    SlotUseBeforeAlloc {
        var: VariablePtr,
        #[label]
        span: Option<SourceSpan>,
    },
    #[error("result seen in function without return slot set")]
    ResultWithoutReturnSlot {
        expr: ExprPtr,
        #[label]
        span: Option<SourceSpan>,
    },
    #[error("`self` was used in a context where self is not defined")]
    SelfInItemWithout { expr: ExprPtr, span: Option<SourceSpan> },
}

#[salsa::accumulator]
pub struct MirErrors(MirError);

impl MirError {
    pub fn populate_spans(
        &mut self,
        expr_f: impl Fn(ExprPtr) -> Option<SourceSpan>,
        var_f: impl Fn(VariablePtr) -> Option<SourceSpan>,
    ) {
        match self {
            MirError::NotYetImplemented { msg: _, expr, span } => *span = expr_f(*expr),
            MirError::SlotUseBeforeAlloc { var, span } => *span = var_f(*var),
            MirError::ResultWithoutReturnSlot { expr, span } => *span = expr_f(*expr),
            MirError::SelfInItemWithout { expr, span } => *span = expr_f(*expr),
        }
    }
}
