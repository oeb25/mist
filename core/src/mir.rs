pub mod analysis;
mod lower;
pub mod optimize;
pub mod serialize;

use std::collections::HashMap;

use derive_more::Display;
use derive_new::new;
use la_arena::{Arena, ArenaMap, Idx};
use mist_syntax::ast::operators::{BinaryOp, UnaryOp};

use crate::hir::{AssertionKind, ExprIdx, Field, Literal, Quantifier, Struct, VariableIdx};

pub use self::lower::{lower_item, lower_program};

pub type BlockId = Idx<Block>;
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    instructions: Vec<InstructionId>,
    dest: Option<SlotId>,
}

impl Block {
    pub fn instructions(&self) -> &[InstructionId] {
        self.instructions.as_ref()
    }

    pub fn dest(&self) -> Option<SlotId> {
        self.dest
    }
}

pub type InstructionId = Idx<Instruction>;
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Instruction {
    Assign(SlotId, MExpr),
    If(SlotId, BlockId, BlockId),
    While(SlotId, Vec<BlockId>, BlockId),
    Assertion(AssertionKind, SlotId),
    Call(FunctionId, Vec<SlotId>),
    Return,
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
    Quantifier(SlotId, Quantifier, Vec<SlotId>, BlockId),
}
impl MExpr {
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
            MExpr::Quantifier(t, q, params, b) => {
                MExpr::Quantifier(map(*t), *q, params.iter().copied().map(map).collect(), *b)
            }
        }
    }

    fn contains_side_effects(&self) -> bool {
        match self {
            MExpr::Call(_, _) => true,
            MExpr::Literal(_)
            | MExpr::Field(_, _)
            | MExpr::Struct(_, _)
            | MExpr::Slot(_)
            | MExpr::Quantifier(_, _, _, _) => false,
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
    BinaryOp(BinaryOp),
    UnaryOp(UnaryOp),
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

#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub struct Body {
    blocks: Arena<Block>,
    instructions: Arena<Instruction>,
    slots: Arena<Slot>,
    functions: Arena<Function>,

    requires: Vec<BlockId>,
    ensures: Vec<BlockId>,
    invariants: Vec<BlockId>,

    result_slot: Option<SlotId>,
    body_block: Option<BlockId>,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct BodySourceMap {
    expr_instr_map: ArenaMap<ExprIdx, Vec<InstructionId>>,
    expr_block_map: ArenaMap<ExprIdx, BlockId>,
    var_map: HashMap<VariableIdx, SlotId>,
}

impl Body {
    pub fn result_slot(&self) -> Option<SlotId> {
        self.result_slot
    }

    pub fn body_block(&self) -> Option<BlockId> {
        self.body_block
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
