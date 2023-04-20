pub mod analysis;
mod lower;
pub mod serialize;

use derive_more::Display;
use derive_new::new;
use itertools::Either;
use la_arena::{Arena, ArenaMap, Idx};
use miette::Diagnostic;
use mist_syntax::{
    ast::operators::{BinaryOp, UnaryOp},
    SourceSpan,
};
use tracing::debug;

use crate::hir::{
    self, AssertionKind, ExprIdx, Field, Literal, Quantifier, Struct, Type, VariableIdx,
};

pub use self::lower::{lower_item, lower_program};

pub type BlockId = Idx<Block>;
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    instructions: Vec<InstructionId>,
    terminator: Option<Terminator>,
}

impl Block {
    pub fn instructions(&self) -> &[InstructionId] {
        self.instructions.as_ref()
    }

    pub fn terminator(&self) -> Option<&Terminator> {
        self.terminator.as_ref()
    }

    fn set_terminator(&mut self, term: Terminator) -> Option<Terminator> {
        let old = self.terminator.replace(term);
        if let Some(_old) = &old {
            debug!("terminator was replaced!");
        }
        old
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Terminator {
    Return,
    Goto(BlockId),
    Quantify(Quantifier, Vec<SlotId>, BlockId),
    QuantifyEnd(BlockId),
    Switch(Operand, SwitchTargets),
    Call {
        func: FunctionId,
        args: Vec<Operand>,
        destination: SlotId,
        target: Option<BlockId>,
    },
}

impl Terminator {
    /// If this replaces an existing target, that target is returned
    pub fn set_target(&mut self, bid: BlockId) -> Option<BlockId> {
        match self {
            Terminator::Return => None,
            Terminator::Goto(t) => Some(std::mem::replace(t, bid)),
            Terminator::Quantify(_, _, t) => Some(std::mem::replace(t, bid)),
            Terminator::QuantifyEnd(t) => Some(std::mem::replace(t, bid)),
            Terminator::Switch(_, _) => {
                // TODO
                None
            }
            Terminator::Call { target, .. } => std::mem::replace(target, Some(bid)),
        }
    }
    pub fn targets(&self) -> Vec<BlockId> {
        match self {
            Terminator::Return => vec![],
            Terminator::Goto(b) => vec![*b],
            Terminator::Quantify(_, _, b) => vec![*b],
            Terminator::QuantifyEnd(b) => vec![*b],
            Terminator::Switch(_, switch) => switch.targets.values().copied().collect(),
            Terminator::Call { target, .. } => target.iter().copied().collect(),
        }
    }
}

pub type Operand = SlotId;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SwitchTargets {
    values: Arena<u128>,
    targets: ArenaMap<Idx<u128>, BlockId>,
    otherwise: BlockId,
}
impl SwitchTargets {
    fn new<const N: usize>(success: [(u128, BlockId); N], otherwise: BlockId) -> SwitchTargets {
        let mut values = Arena::default();
        let mut targets = ArenaMap::default();
        for (v, bid) in success {
            targets.insert(values.alloc(v), bid);
        }

        SwitchTargets {
            values,
            targets,
            otherwise,
        }
    }
    pub fn values(&self) -> (impl Iterator<Item = (u128, BlockId)> + '_, BlockId) {
        (
            self.targets.iter().map(|(v, t)| (self.values[v], *t)),
            self.otherwise,
        )
    }

    pub fn has_values(&self) -> bool {
        !self.values.is_empty()
    }
}

pub type InstructionId = Idx<Instruction>;
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Instruction {
    Assign(SlotId, MExpr),
    Assertion(AssertionKind, SlotId),
}

pub type SlotId = Idx<Slot>;
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub enum Slot {
    #[default]
    Temp,
    Var(VariableIdx),
    Literal(Literal),
    Result,
}
impl Slot {
    fn from_var(var: VariableIdx) -> Self {
        Self::Var(var)
    }

    #[must_use]
    pub fn is_result(&self) -> bool {
        matches!(self, Self::Result)
    }

    #[must_use]
    pub fn is_literal(&self) -> bool {
        matches!(self, Self::Literal(..))
    }

    pub fn as_literal(&self) -> Option<&Literal> {
        if let Self::Literal(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MExpr {
    Literal(Literal),
    Call(FunctionId, Vec<SlotId>),
    Field(SlotId, Field),
    Struct(Struct, Vec<(Field, SlotId)>),
    Slot(SlotId),
    BinaryOp(BinaryOp, Operand, Operand),
    UnaryOp(UnaryOp, Operand),
}
impl MExpr {
    #[allow(dead_code)]
    fn map_slots(&self, mut map: impl FnMut(SlotId) -> SlotId) -> MExpr {
        match self {
            MExpr::Literal(_) => self.clone(),
            MExpr::Call(f, args) => MExpr::Call(*f, args.iter().copied().map(&mut map).collect()),
            MExpr::Field(s, f) => MExpr::Field(map(*s), f.clone()),
            MExpr::Struct(st, fields) => MExpr::Struct(
                *st,
                fields.iter().map(|(f, s)| (f.clone(), map(*s))).collect(),
            ),
            MExpr::Slot(s) => MExpr::Slot(map(*s)),
            MExpr::BinaryOp(op, l, r) => MExpr::BinaryOp(*op, map(*l), map(*r)),
            MExpr::UnaryOp(op, o) => MExpr::UnaryOp(*op, map(*o)),
        }
    }

    #[allow(dead_code)]
    fn contains_side_effects(&self) -> bool {
        match self {
            MExpr::Call(_, _) => true,
            MExpr::Literal(_)
            | MExpr::Field(_, _)
            | MExpr::Struct(_, _)
            | MExpr::Slot(_)
            | MExpr::BinaryOp(_, _, _)
            | MExpr::UnaryOp(_, _) => false,
        }
    }
}

pub type FunctionId = Idx<Function>;
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    data: FunctionData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionData {
    Named(VariableIdx),
    Index,
    RangeIndex,
    Range(RangeKind),
    List,
}

impl std::ops::Deref for Function {
    type Target = FunctionData;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
pub enum RangeKind {
    #[display(fmt = "from-to")]
    FromTo,
    #[display(fmt = "from")]
    From,
    #[display(fmt = "to")]
    To,
    #[display(fmt = "full")]
    Full,
}

#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Body {
    item_id: hir::ItemId,

    #[new(default)]
    blocks: Arena<Block>,
    #[new(default)]
    instructions: Arena<Instruction>,
    #[new(default)]
    slots: Arena<Slot>,
    #[new(default)]
    functions: Arena<Function>,

    #[new(default)]
    params: Vec<SlotId>,

    #[new(default)]
    block_invariants: ArenaMap<BlockId, Vec<BlockId>>,
    #[new(default)]
    slot_type: ArenaMap<SlotId, Type>,

    #[new(default)]
    requires: Vec<BlockId>,
    #[new(default)]
    ensures: Vec<BlockId>,
    #[new(default)]
    invariants: Vec<BlockId>,

    #[new(default)]
    result_slot: Option<SlotId>,
    #[new(default)]
    body_block: Option<BlockId>,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct BodySourceMap {
    pub expr_instr_map: ArenaMap<ExprIdx, Vec<InstructionId>>,
    expr_instr_map_back: ArenaMap<InstructionId, ExprIdx>,
    pub expr_block_map: ArenaMap<ExprIdx, BlockId>,
    expr_block_map_back: ArenaMap<BlockId, ExprIdx>,
    pub var_map: ArenaMap<VariableIdx, SlotId>,
}

impl BodySourceMap {
    pub fn trace_expr(&self, instr_or_block: impl Into<BlockOrInstruction>) -> Option<ExprIdx> {
        match instr_or_block.into() {
            BlockOrInstruction::Block(b) => self.expr_block_map_back.get(b).copied(),
            BlockOrInstruction::Instruction(b) => self.expr_instr_map_back.get(b).copied(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, derive_more::From)]
pub enum BlockOrInstruction {
    Block(BlockId),
    Instruction(InstructionId),
}

impl Body {
    pub fn result_slot(&self) -> Option<SlotId> {
        self.result_slot
    }

    pub fn body_block(&self) -> Option<BlockId> {
        self.body_block
    }

    pub fn requires(&self) -> &[Idx<Block>] {
        self.requires.as_ref()
    }

    pub fn ensures(&self) -> &[Idx<Block>] {
        self.ensures.as_ref()
    }

    pub fn invariants(&self) -> &[Idx<Block>] {
        self.invariants.as_ref()
    }

    pub fn assignments_to(&self, x: SlotId) -> impl Iterator<Item = InstructionId> + '_ {
        self.instructions
            .iter()
            .filter_map(move |(id, inst)| match inst {
                Instruction::Assign(y, _) if x == *y => Some(id),
                _ => None,
            })
    }
    pub fn reference_to(
        &self,
        x: SlotId,
    ) -> impl Iterator<Item = Either<InstructionId, &Terminator>> + '_ {
        self.instructions
            .iter()
            .filter_map(move |(id, inst)| match inst {
                Instruction::Assign(_, e) if e.all_slot_usages().into_iter().any(|y| x == y) => {
                    Some(id)
                }
                Instruction::Assertion(_, y) if x == *y => Some(id),
                _ => None,
            })
            .map(Either::Left)
            .chain(
                self.blocks
                    .iter()
                    .filter_map(move |(_, b)| {
                        let term = b.terminator()?;
                        match term {
                            Terminator::Quantify(_, over, _) => over.contains(&x).then_some(term),
                            Terminator::Switch(op, _) => (x == *op).then_some(term),
                            Terminator::Call { args, .. } => args.contains(&x).then_some(term),

                            Terminator::Return
                            | Terminator::Goto(_)
                            | Terminator::QuantifyEnd(_) => None,
                        }
                    })
                    .map(Either::Right),
            )
    }

    pub fn params(&self) -> &[SlotId] {
        self.params.as_ref()
    }

    pub fn slot_ty(&self, slot: SlotId) -> hir::Type {
        self.slot_type[slot]
    }

    pub fn slots(&self) -> impl Iterator<Item = SlotId> + '_ {
        self.slots.iter().map(|(id, _)| id)
    }

    pub fn item_id(&self) -> hir::ItemId {
        self.item_id
    }

    pub fn block_invariants(&self, block: BlockId) -> &[BlockId] {
        &self.block_invariants[block]
    }
}

impl std::ops::Index<BlockId> for Body {
    type Output = Block;

    fn index(&self, index: BlockId) -> &Self::Output {
        &self.blocks[index]
    }
}
impl std::ops::Index<&'_ BlockId> for Body {
    type Output = Block;

    fn index(&self, index: &'_ BlockId) -> &Self::Output {
        &self.blocks[*index]
    }
}
impl std::ops::Index<InstructionId> for Body {
    type Output = Instruction;

    fn index(&self, index: InstructionId) -> &Self::Output {
        &self.instructions[index]
    }
}
impl std::ops::Index<&'_ InstructionId> for Body {
    type Output = Instruction;

    fn index(&self, index: &'_ InstructionId) -> &Self::Output {
        &self.instructions[*index]
    }
}
impl std::ops::Index<SlotId> for Body {
    type Output = Slot;

    fn index(&self, index: SlotId) -> &Self::Output {
        &self.slots[index]
    }
}
impl std::ops::Index<&'_ SlotId> for Body {
    type Output = Slot;

    fn index(&self, index: &'_ SlotId) -> &Self::Output {
        &self.slots[*index]
    }
}
impl std::ops::Index<FunctionId> for Body {
    type Output = Function;

    fn index(&self, index: FunctionId) -> &Self::Output {
        &self.functions[index]
    }
}
impl std::ops::Index<&'_ FunctionId> for Body {
    type Output = Function;

    fn index(&self, index: &'_ FunctionId) -> &Self::Output {
        &self.functions[*index]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error, Diagnostic)]
pub enum MirError {
    #[error("not yet implemented: {_0}")]
    NotYetImplemented(String),
    #[error("variable used before its slot was allocated")]
    SlotUseBeforeAlloc {
        var: VariableIdx,
        #[label]
        span: Option<SourceSpan>,
    },
    #[error("result seen in function without return slot set")]
    ResultWithoutReturnSlot {
        expr: hir::ExprIdx,
        #[label]
        span: Option<SourceSpan>,
    },
}

#[salsa::accumulator]
pub struct MirErrors(MirError);

impl MirError {
    pub fn populate_spans(&mut self, cx: &hir::ItemContext, source_map: &hir::ItemSourceMap) {
        match self {
            MirError::NotYetImplemented(_) => {}
            MirError::SlotUseBeforeAlloc { var, span } => {
                *span = Some(cx.var_span(*var));
            }
            MirError::ResultWithoutReturnSlot { expr, span } => {
                *span = Some(source_map.expr_span(*expr))
            }
        }
    }
}
