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

use crate::hir::{self, AssertionKind, Field, Literal, Quantifier, Struct, Type, VariableIdx};

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
        destination: Place,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Literal(Literal),
}
impl Operand {
    fn place(&self) -> Option<Place> {
        match self {
            Operand::Copy(s) | Operand::Move(s) => Some(*s),
            Operand::Literal(_) => None,
        }
    }
    fn slot(&self) -> Option<SlotId> {
        self.place().map(|s| s.slot)
    }
}

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
    Assign(Place, MExpr),
    Assertion(AssertionKind, MExpr),
}

pub type SlotId = Idx<Slot>;
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub enum Slot {
    #[default]
    Temp,
    Var(VariableIdx),
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
}

pub type PlaceId = Idx<Place>;
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Place {
    pub slot: SlotId,
    pub projection: ProjectionList,
}

impl From<SlotId> for Place {
    fn from(slot: SlotId) -> Self {
        Place {
            slot,
            projection: ProjectionList::from_raw(0.into()),
        }
    }
}

pub type ProjectionList = Idx<Vec<Projection>>;
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Projection {
    Field(Field, hir::Type),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MExpr {
    Struct(Struct, Vec<(Field, Operand)>),
    Use(Operand),
    BinaryOp(BinaryOp, Operand, Operand),
    UnaryOp(UnaryOp, Operand),
}
impl MExpr {
    #[allow(dead_code)]
    fn map_slots(&self, mut map: impl FnMut(&Operand) -> Operand) -> MExpr {
        match self {
            MExpr::Struct(st, fields) => MExpr::Struct(
                *st,
                fields.iter().map(|(f, o)| (f.clone(), map(o))).collect(),
            ),
            MExpr::Use(o) => MExpr::Use(map(o)),
            MExpr::BinaryOp(op, l, r) => MExpr::BinaryOp(*op, map(l), map(r)),
            MExpr::UnaryOp(op, o) => MExpr::UnaryOp(*op, map(o)),
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
    #[new(value = "{ let mut arena = Arena::new(); arena.alloc(vec![]); arena }")]
    projections: Arena<Vec<Projection>>,
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
    pub expr_instr_map: ArenaMap<hir::ExprIdx, Vec<InstructionId>>,
    expr_instr_map_back: ArenaMap<InstructionId, hir::ExprIdx>,
    pub expr_block_map: ArenaMap<hir::ExprIdx, BlockId>,
    expr_block_map_back: ArenaMap<BlockId, hir::ExprIdx>,
    pub var_map: ArenaMap<VariableIdx, SlotId>,
}

impl BodySourceMap {
    pub fn trace_expr(
        &self,
        instr_or_block: impl Into<BlockOrInstruction>,
    ) -> Option<hir::ExprIdx> {
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
                Instruction::Assign(y, _) if x == y.slot => Some(id),
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
                Instruction::Assign(_, e) | Instruction::Assertion(_, e)
                    if e.all_slot_usages().into_iter().any(|y| x == y) =>
                {
                    Some(id)
                }
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
                            Terminator::Switch(op, _) => (Some(x) == op.slot()).then_some(term),
                            Terminator::Call { args, .. } => {
                                args.iter().any(|arg| Some(x) == arg.slot()).then_some(term)
                            }

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

    pub fn place_ty(&self, place: Place) -> hir::Type {
        if self[place.projection].is_empty() {
            self.slot_ty(place.slot)
        } else {
            match self[place.projection].last().unwrap() {
                Projection::Field(_, ty) => *ty,
            }
        }
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
impl std::ops::Index<ProjectionList> for Body {
    type Output = [Projection];

    fn index(&self, index: ProjectionList) -> &Self::Output {
        &self.projections[index]
    }
}
impl std::ops::Index<&'_ ProjectionList> for Body {
    type Output = [Projection];

    fn index(&self, index: &'_ ProjectionList) -> &Self::Output {
        &self.projections[*index]
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
    #[error("not yet implemented: {msg}")]
    NotYetImplemented {
        msg: String,
        item_id: hir::ItemId,
        expr: hir::ExprIdx,
        #[label]
        span: Option<SourceSpan>,
    },
    #[error("variable used before its slot was allocated")]
    SlotUseBeforeAlloc {
        item_id: hir::ItemId,
        var: VariableIdx,
        #[label]
        span: Option<SourceSpan>,
    },
    #[error("result seen in function without return slot set")]
    ResultWithoutReturnSlot {
        item_id: hir::ItemId,
        expr: hir::ExprIdx,
        #[label]
        span: Option<SourceSpan>,
    },
}

#[salsa::accumulator]
pub struct MirErrors(MirError);

impl MirError {
    pub fn populate_spans(
        &mut self,
        expr_f: impl Fn(hir::ItemId, hir::ExprIdx) -> Option<SourceSpan>,
        var_f: impl Fn(hir::ItemId, hir::VariableIdx) -> Option<SourceSpan>,
    ) {
        match self {
            MirError::NotYetImplemented {
                msg: _,
                item_id,
                expr,
                span,
            } => *span = expr_f(*item_id, *expr),
            MirError::SlotUseBeforeAlloc { item_id, var, span } => *span = var_f(*item_id, *var),
            MirError::ResultWithoutReturnSlot {
                item_id,
                expr,
                span,
            } => *span = expr_f(*item_id, *expr),
        }
    }
}
