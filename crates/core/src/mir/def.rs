mod ext;
pub mod lower;
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
    types::BuiltinField,
    util::{impl_idx, IdxArena, IdxMap},
};

use place::{Place, SlotId};

impl_idx!(BlockId, Block);
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    instructions: Vec<InstructionId>,
    terminator: Option<Terminator>,
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
    BuiltinMethod(BuiltinField<Type>),
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
pub struct ItemBody {
    item: Item,

    body: Body,

    params: Vec<SlotId>,

    requires: Vec<BlockId>,
    ensures: Vec<BlockId>,
    invariants: Vec<BlockId>,

    body_block: Option<BlockId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Body {
    item: Item,

    self_slot: Option<SlotId>,
    result_slot: Option<SlotId>,

    blocks: IdxArena<BlockId>,
    instructions: IdxArena<InstructionId>,
    slots: IdxArena<SlotId>,
    block_invariants: IdxMap<BlockId, Vec<BlockId>>,
    slot_type: IdxMap<SlotId, Type>,
}

impl std::ops::Deref for ItemBody {
    type Target = Body;

    fn deref(&self) -> &Self::Target {
        &self.body
    }
}
impl std::ops::DerefMut for ItemBody {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.body
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, From)]
pub enum BlockOrInstruction {
    Block(BlockId),
    Instruction(InstructionId),
}

pub type BodyLocation = InBlock<BlockLocation>;

#[derive(new, Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub struct InBlock<T> {
    pub bid: BlockId,
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
