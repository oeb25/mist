mod ext;
pub mod place;
pub mod source_map;

use derive_more::{Display, From};
use derive_new::new;
use la_arena::{Arena, ArenaMap, Idx};
use mist_syntax::ast::operators::{BinaryOp, UnaryOp};

use crate::{
    hir::{AssertionKind, Literal, Quantifier},
    mono::{
        exprs::VariablePtr,
        types::{Adt, AdtField, Type},
        Item,
    },
    util::{impl_idx, IdxArena, IdxMap},
};

use place::{Place, SlotId};

impl_idx!(BlockId, Block);
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    pub(super) instructions: Vec<InstructionId>,
    pub(super) terminator: Option<Terminator>,
}

#[salsa::interned]
pub struct Terminator {
    #[return_ref]
    pub kind: TerminatorKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TerminatorKind {
    Return,
    Goto(BlockId),
    Quantify(Quantifier, Vec<SlotId>, BlockId),
    QuantifyEnd(BlockId),
    Switch(Operand, SwitchTargets),
    Call { func: Function, args: Vec<Operand>, destination: Place, target: Option<BlockId> },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Literal(Literal),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SwitchTargets {
    values: Arena<u128>,
    targets: ArenaMap<Idx<u128>, BlockId>,
    otherwise: BlockId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Folding {
    Fold { into: Place },
    Unfold { consume: Place },
}

impl_idx!(InstructionId, Instruction, default_debug);
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Instruction {
    Assign(Place, MExpr),
    NewAdt(Place, Adt, Vec<(AdtField, Operand)>),
    Assertion(AssertionKind, MExpr),
    Folding(Folding),
    PlaceMention(Place),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BorrowKind {
    Shared,
    Mutable,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MExpr {
    Use(Operand),
    Ref(BorrowKind, Place),
    BinaryOp(BinaryOp, Operand, Operand),
    UnaryOp(UnaryOp, Operand),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Function {
    Named(VariablePtr),
    Index,
    RangeIndex,
    Range(RangeKind),
    InRange,
    RangeMin,
    RangeMax,
    List,
    ListConcat,
}

#[derive(Debug, Display, Clone, Copy, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Body {
    item: Item,

    pub(super) self_slot: SlotId,

    pub(super) blocks: IdxArena<BlockId>,
    pub(super) instructions: IdxArena<InstructionId>,
    pub(super) slots: IdxArena<SlotId>,

    pub(super) params: Vec<SlotId>,

    pub(super) block_invariants: IdxMap<BlockId, Vec<BlockId>>,
    pub(super) slot_type: IdxMap<SlotId, Type>,

    pub(super) requires: Vec<BlockId>,
    pub(super) ensures: Vec<BlockId>,
    pub(super) invariants: Vec<BlockId>,

    pub(super) result_slot: Option<SlotId>,
    pub(super) body_block: Option<BlockId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, From)]
pub enum BlockOrInstruction {
    Block(BlockId),
    Instruction(InstructionId),
}

pub type BodyLocation = InBlock<BlockLocation>;

#[derive(new, Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub struct InBlock<T> {
    pub block: BlockId,
    pub inner: T,
}

pub type BlockLocation = Action<()>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Action<T = Terminator> {
    Instruction(InstructionId),
    Terminator(T),
}

impl<T> From<InstructionId> for Action<T> {
    fn from(inst: InstructionId) -> Self {
        Action::Instruction(inst)
    }
}

impl From<Terminator> for Action {
    fn from(t: Terminator) -> Self {
        Action::Terminator(t)
    }
}
