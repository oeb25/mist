pub mod analysis;
mod lower;
pub mod pass;
pub mod serialize;

use std::{collections::HashMap, fmt};

use derive_more::{Display, From};
use derive_new::new;
use itertools::Either::{self, Left, Right};
use la_arena::{Arena, ArenaMap, Idx};
use miette::Diagnostic;
use mist_syntax::{
    ast::operators::{BinaryOp, UnaryOp},
    SourceSpan,
};
use tracing::debug;

use crate::{
    hir::{AssertionKind, Literal, Quantifier},
    mono::{
        exprs::{ExprPtr, Field, VariablePtr},
        types::{Adt, AdtField, Type},
        Item,
    },
    util::{impl_idx, IdxArena, IdxMap, IdxWrap},
};

pub use self::lower::lower_item;

#[salsa::tracked]
pub struct ItemMir {
    #[return_ref]
    pub body: Body,
    #[return_ref]
    pub source_map: BodySourceMap,
}

impl_idx!(BlockId, Block);
impl fmt::Debug for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ":B{}", self.0.into_raw())
    }
}
impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ":B{}", self.0.into_raw())
    }
}
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

    pub fn first_loc(&self) -> BlockLocation {
        self.instructions
            .iter()
            .copied()
            .map(BlockLocation::Instruction)
            .next()
            .unwrap_or(BlockLocation::Terminator)
    }

    pub fn locations(&self) -> impl Iterator<Item = BlockLocation> + '_ {
        self.instructions
            .iter()
            .copied()
            .map(BlockLocation::Instruction)
            .chain(self.terminator.is_some().then_some(BlockLocation::Terminator))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Terminator {
    Return,
    Goto(BlockId),
    Quantify(Quantifier, Vec<SlotId>, BlockId),
    QuantifyEnd(BlockId),
    Switch(Operand, SwitchTargets),
    Call { func: FunctionId, args: Vec<Operand>, destination: Place, target: Option<BlockId> },
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
            Terminator::Switch(_, switch) => {
                switch.targets.values().copied().chain([switch.otherwise]).collect()
            }
            Terminator::Call { target, .. } => target.iter().copied().collect(),
        }
    }
    pub fn map_targets_mut(&mut self, mut f: impl FnMut(BlockId) -> BlockId) {
        match self {
            Terminator::Return => {}
            Terminator::Goto(b) | Terminator::Quantify(_, _, b) | Terminator::QuantifyEnd(b) => {
                *b = f(*b)
            }
            Terminator::Switch(_, switch) => {
                for (_, t) in switch.targets.iter_mut() {
                    *t = f(*t);
                }
                switch.otherwise = f(switch.otherwise)
            }
            Terminator::Call { target, .. } => {
                if let Some(b) = target {
                    *b = f(*b)
                }
            }
        }
    }

    fn places_referenced<'a>(&'a self, body: &'a Body) -> impl Iterator<Item = Place> + 'a {
        match self {
            Terminator::Return
            | Terminator::Goto(_)
            | Terminator::Quantify(_, _, _)
            | Terminator::QuantifyEnd(_) => Left(None.into_iter()),
            Terminator::Switch(op, _) => Left(op.place().into_iter()),
            Terminator::Call { args, .. } => Right(args.iter().filter_map(|arg| arg.place())),
        }
        .flat_map(|p| [p].into_iter().chain(nested_places(p, body)))
    }

    fn places_written_to(&self) -> impl Iterator<Item = Place> + '_ {
        match self {
            Terminator::Call { destination, .. } => Left([*destination].into_iter()),
            Terminator::Return
            | Terminator::Goto(_)
            | Terminator::Quantify(_, _, _)
            | Terminator::QuantifyEnd(_)
            | Terminator::Switch(_, _) => Right([].into_iter()),
        }
    }

    fn places(&self) -> impl Iterator<Item = Place> + '_ {
        match self {
            Terminator::Return
            | Terminator::Goto(_)
            | Terminator::Quantify(_, _, _)
            | Terminator::QuantifyEnd(_) => Left(None.into_iter()),
            Terminator::Switch(op, _) => Left(op.place().into_iter()),
            Terminator::Call { args, destination, .. } => {
                Right(args.iter().filter_map(|arg| arg.place()).chain([*destination]))
            }
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

        SwitchTargets { values, targets, otherwise }
    }
    pub fn values(&self) -> (impl Iterator<Item = (u128, BlockId)> + '_, BlockId) {
        (self.targets.iter().map(|(v, t)| (self.values[v], *t)), self.otherwise)
    }
    pub fn targets(&self) -> (impl Iterator<Item = BlockId> + '_, BlockId) {
        (self.targets.iter().map(|(_, b)| *b), self.otherwise)
    }

    pub fn has_values(&self) -> bool {
        !self.values.is_empty()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Folding {
    Fold { into: Place },
    Unfold { consume: Place },
}

impl Folding {
    pub fn place(self) -> Place {
        match self {
            Folding::Fold { into } => into,
            Folding::Unfold { consume } => consume,
        }
    }
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

impl_idx!(SlotId, Slot);
impl fmt::Debug for SlotId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.0.into_raw())
    }
}
impl fmt::Display for SlotId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "%{}", self.0.into_raw())
    }
}
#[derive(Debug, Default, Clone, PartialEq, Eq, Hash)]
pub enum Slot {
    #[default]
    Temp,
    Self_,
    Param(VariablePtr),
    Local(VariablePtr),
    Quantified(VariablePtr),
    Result,
}
impl Slot {
    #[must_use]
    pub fn is_result(&self) -> bool {
        matches!(self, Self::Result)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Place {
    pub slot: SlotId,
    pub projection: ProjectionList,
}
impl Place {
    pub fn without_projection(&self) -> Place {
        self.replace_projection(Projection::empty())
    }

    pub fn replace_projection(&self, projection: ProjectionList) -> Place {
        Place { slot: self.slot, projection }
    }

    pub fn parent(&self, b: &Body) -> Option<Place> {
        Some(self.replace_projection(b.projection_parent(self.projection)?))
    }
}

impl From<SlotId> for Place {
    fn from(slot: SlotId) -> Self {
        Place { slot, projection: Projection::empty() }
    }
}

impl_idx!(ProjectionList, Vec<Projection>, default_debug);
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Projection {
    Field(Field, Type),
    Index(SlotId, Type),
}
impl Projection {
    /// Construct an empty [`ProjectionList`]
    pub fn empty() -> ProjectionList {
        ProjectionList::from_raw(0.into())
    }
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
impl MExpr {
    #[allow(dead_code)]
    fn map_operand(&self, mut map: impl FnMut(&Operand) -> Operand) -> MExpr {
        match self {
            MExpr::Use(o) => MExpr::Use(map(o)),
            MExpr::Ref(bk, o) => MExpr::Ref(*bk, *o),
            MExpr::BinaryOp(op, l, r) => MExpr::BinaryOp(*op, map(l), map(r)),
            MExpr::UnaryOp(op, o) => MExpr::UnaryOp(*op, map(o)),
        }
    }
}

impl_idx!(FunctionId, Function, default_debug);
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function {
    data: FunctionData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionData {
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Body {
    item: Item,

    self_slot: SlotId,

    blocks: IdxArena<BlockId>,
    instructions: IdxArena<InstructionId>,
    slots: IdxArena<SlotId>,
    projections: IdxArena<ProjectionList>,
    functions: IdxArena<FunctionId>,

    params: Vec<SlotId>,

    block_invariants: IdxMap<BlockId, Vec<BlockId>>,
    slot_type: IdxMap<SlotId, Type>,

    requires: Vec<BlockId>,
    ensures: Vec<BlockId>,
    invariants: Vec<BlockId>,

    result_slot: Option<SlotId>,
    body_block: Option<BlockId>,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct BodySourceMap {
    pub expr_instr_map: HashMap<ExprPtr, Vec<InstructionId>>,
    expr_instr_map_back: IdxMap<InstructionId, ExprPtr>,
    pub expr_block_map: HashMap<ExprPtr, BlockId>,
    expr_block_map_back: IdxMap<BlockId, ExprPtr>,
    pub var_map: HashMap<VariablePtr, SlotId>,
}

impl BodySourceMap {
    pub fn trace_expr(&self, instr_or_block: impl Into<BlockOrInstruction>) -> Option<ExprPtr> {
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
    fn new(item: Item) -> Body {
        let mut slots: IdxArena<_> = Default::default();
        let self_slot = slots.alloc(Slot::Self_);

        Body {
            item,

            self_slot,

            blocks: Default::default(),
            instructions: Default::default(),
            slots,
            projections: {
                let mut arena = IdxArena::default();
                arena.alloc(vec![]);
                arena
            },
            functions: Default::default(),

            params: Default::default(),

            block_invariants: Default::default(),
            slot_type: Default::default(),

            requires: Default::default(),
            ensures: Default::default(),
            invariants: Default::default(),

            result_slot: Default::default(),
            body_block: Default::default(),
        }
    }

    pub fn result_slot(&self) -> Option<SlotId> {
        self.result_slot
    }
    pub fn self_slot(&self) -> SlotId {
        self.self_slot
    }

    pub fn entry_blocks(&self) -> impl Iterator<Item = BlockId> + '_ {
        itertools::chain!(
            itertools::chain!(self.requires(), self.invariants(), self.ensures()).copied(),
            self.body_block(),
            self.block_invariants.iter().flat_map(|(_, invs)| invs).copied()
        )
    }
    pub fn is_requires(&self, bid: BlockId) -> bool {
        self.requires.contains(&bid)
    }
    pub fn is_ensures(&self, bid: BlockId) -> bool {
        self.ensures.contains(&bid)
    }

    fn exit_blocks(&self) -> impl Iterator<Item = BlockId> + '_ {
        self.blocks.iter().filter_map(|(bid, b)| match &b.terminator {
            Some(t) => t.targets().is_empty().then_some(bid),
            None => Some(bid),
        })
    }

    pub fn body_block(&self) -> Option<BlockId> {
        self.body_block
    }

    pub fn requires(&self) -> &[BlockId] {
        self.requires.as_ref()
    }

    pub fn ensures(&self) -> &[BlockId] {
        self.ensures.as_ref()
    }

    pub fn invariants(&self) -> &[BlockId] {
        self.invariants.as_ref()
    }

    pub fn assignments_to(&self, x: SlotId) -> impl Iterator<Item = InstructionId> + '_ {
        self.instructions.iter().filter_map(move |(id, inst)| match inst {
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
            .map(Left)
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
                    .map(Right),
            )
    }

    pub fn params(&self) -> &[SlotId] {
        self.params.as_ref()
    }

    pub fn slot_ty(&self, db: &dyn crate::Db, slot: SlotId) -> Type {
        self.slot_type.get(slot).copied().unwrap_or_else(|| Type::error(db))
    }

    pub fn place_ty(&self, db: &dyn crate::Db, place: Place) -> Type {
        if self[place.projection].is_empty() {
            self.slot_ty(db, place.slot)
        } else {
            match self[place.projection].last().unwrap() {
                Projection::Field(_, ty) | Projection::Index(_, ty) => *ty,
            }
        }
    }

    pub fn def(&self) -> Item {
        self.item
    }

    pub fn block_invariants(&self, block: BlockId) -> &[BlockId] {
        self.block_invariants.get(block).map(|invs| invs.as_slice()).unwrap_or_else(|| &[])
    }

    /// Returns a iterator over all [`ProjectionList`]'s leading to this projection.
    ///
    /// For `a.b.c` the iterator will produce `[a, a.b, a.b.c]` in that order.
    pub fn projection_path_iter(
        &self,
        projection: ProjectionList,
    ) -> impl Iterator<Item = ProjectionList> + '_ {
        let mut entries = vec![projection];
        let mut current = projection;

        loop {
            match self.projection_parent(current) {
                Some(next) => {
                    entries.push(next);
                    current = next;
                }
                None => {
                    return entries.into_iter().rev();
                }
            }
        }
    }
    pub fn projection_parent(&self, projection: ProjectionList) -> Option<ProjectionList> {
        let list = &self[projection];
        let search_for = if list.is_empty() {
            return None;
        } else {
            &list[0..list.len() - 1]
        };
        Some(self.projections.iter().find(|(_, proj)| proj == &search_for).unwrap().0)
    }

    fn intersperse_block(&mut self, from: BlockId, into: BlockId, middle: BlockId) {
        let Some(t) = &mut self.blocks[from].terminator else { return };
        t.map_targets_mut(|b| if b == into { middle } else { b });
    }
    fn intersperse_instructions(
        &mut self,
        from: BlockId,
        into: BlockId,
        folding: impl Iterator<Item = Instruction>,
    ) {
        let middle = self.blocks.alloc(Block {
            instructions: folding.map(|inst| self.instructions.alloc(inst)).collect(),
            terminator: Some(Terminator::Goto(into)),
        });
        self.intersperse_block(from, into, middle);
        // TODO: It might be useful to append to a current block instead of
        // creating a new everytime:

        // match &self.blocks[from].terminator {
        //     Some(term) => match term {
        //         Terminator::Goto(next) => {
        //             assert_eq!(*next, into);
        //             self.blocks[from]
        //                 .instructions
        //                 .extend(folding.map(|inst| self.instructions.alloc(inst)));
        //         }
        //         Terminator::Return => todo!(),
        //         Terminator::Quantify(_, _, _) => todo!(),
        //         Terminator::QuantifyEnd(_) => todo!(),
        //         Terminator::Switch(_, targets) => {
        //             if into == targets.otherwise {
        //             } else {
        //                 for (_, next_bid) in targets.targets.iter_mut() {
        //                     if into == *next_bid {
        //                         let middle = self.blocks.alloc(Block {
        //                             instructions: folding
        //                                 .map(|inst| self.instructions.alloc(inst))
        //                                 .collect(),
        //                             terminator: Some(Terminator::Goto(into)),
        //                         });
        //                         *next_bid = middle;
        //                     }
        //                 }
        //             }
        //         }
        //         Terminator::Call { target, .. } => {
        //             assert_eq!(*target, Some(into));
        //             let middle = self.blocks.alloc(Block {
        //                 instructions: folding.map(|inst| self.instructions.alloc(inst)).collect(),
        //                 terminator: Some(Terminator::Goto(into)),
        //             });
        //             match &mut self.blocks[from].terminator {
        //                 Some(Terminator::Call { target, .. }) => *target = Some(middle),
        //                 _ => unreachable!(),
        //             }
        //         }
        //     },
        //     None => todo!(),
        // }
    }

    fn slots_referenced<'a>(&'a self, blocks: &'a [BlockId]) -> impl Iterator<Item = SlotId> + 'a {
        blocks.iter().flat_map(|bid| {
            self[*bid]
                .instructions()
                .iter()
                .flat_map(|inst| self[inst].places().map(|p| p.slot))
                .chain(
                    self[*bid]
                        .terminator()
                        .into_iter()
                        .flat_map(|term| term.places().map(|p| p.slot)),
                )
        })
    }

    pub fn preceding_blocks(&self, bid: BlockId) -> impl Iterator<Item = BlockId> + '_ {
        self.blocks
            .iter()
            .filter_map(move |(nbid, b)| b.terminator()?.targets().contains(&bid).then_some(nbid))
    }
    pub fn succeeding_blocks(&self, bid: BlockId) -> impl Iterator<Item = BlockId> + '_ {
        self.blocks[bid].terminator().into_iter().flat_map(|t| t.targets())
    }

    /// Returns an iterator over everything that local to the body. This
    /// includes `Slot::Temp` and `Slot::Local(..)`.
    pub fn locals(&self) -> impl Iterator<Item = SlotId> + '_ {
        self.slots.iter().filter_map(|(sid, slot)| match slot {
            Slot::Temp | Slot::Local(_) => Some(sid),
            _ => None,
        })
    }

    pub fn first_loc_in(&self, bid: BlockId) -> BodyLocation {
        self[bid].first_loc().in_block(bid)
    }

    fn locations_in(&self, bid: BlockId) -> impl Iterator<Item = BodyLocation> + '_ {
        self[bid].locations().map(move |loc| loc.in_block(bid))
    }

    pub fn project_deeper(&mut self, mut place: Place, projection: &[Projection]) -> Place {
        let mut new_projection = self[place.projection].to_vec();
        new_projection.extend_from_slice(projection);

        if let Some((id, _)) = self.projections.iter().find(|(_, proj)| proj == &&new_projection) {
            place.projection = id;
            return place;
        }

        place.projection = self.projections.alloc(new_projection);
        place
    }
}

impl Body {
    fn insert_instruction_before(&mut self, loc: BodyLocation, inst: Instruction) -> InstructionId {
        let insert_idx = match loc.inner {
            BlockLocation::Instruction(inst) => {
                self[loc.block].instructions().iter().position(|&i| i == inst).unwrap()
            }
            BlockLocation::Terminator => self[loc.block].instructions().len(),
        };
        let id = self.instructions.alloc(inst);
        self.blocks[loc.block].instructions.insert(insert_idx, id);
        id
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

#[derive(new, Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub struct BodyLocation {
    pub block: BlockId,
    pub inner: BlockLocation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, From)]
pub enum BlockLocation {
    Instruction(InstructionId),
    Terminator,
}

impl BlockLocation {
    pub fn in_block(self, bid: BlockId) -> BodyLocation {
        BodyLocation { block: bid, inner: self }
    }

    pub fn as_instruction(self) -> Option<InstructionId> {
        if let Self::Instruction(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl Instruction {
    pub fn places(&self) -> impl Iterator<Item = Place> + '_ {
        match self {
            Instruction::Assign(target, expr) => {
                Left(Left([*target].into_iter().chain(Left(expr.places()))))
            }
            Instruction::NewAdt(target, _, fields) => Left(Left(
                [*target].into_iter().chain(Right(fields.iter().flat_map(|f| f.1.place()))),
            )),
            Instruction::Assertion(_, expr) => Left(Right(expr.places())),
            Instruction::PlaceMention(p) => Right([*p].into_iter()),
            Instruction::Folding(folding) => match folding {
                Folding::Fold { into } => Right([*into].into_iter()),
                Folding::Unfold { consume } => Right([*consume].into_iter()),
            },
        }
    }

    fn places_referenced<'a>(&'a self, body: &'a Body) -> impl Iterator<Item = Place> + 'a {
        match self {
            Instruction::Assign(_, expr) => {
                // TODO: Perhaps the targets parent should be part of the
                // referenced as well?
                Left(None.into_iter().chain(Left(expr.places())))
            }
            Instruction::NewAdt(_, _, fields) => {
                Left(None.into_iter().chain(Right(fields.iter().flat_map(|f| f.1.place()))))
            }
            Instruction::Assertion(_, expr) => Left(None.into_iter().chain(Left(expr.places()))),
            Instruction::PlaceMention(p) => Right([*p]),
            Instruction::Folding(folding) => match *folding {
                Folding::Fold { into } => Right([into]),
                Folding::Unfold { consume } => Right([consume]),
            },
        }
        .into_iter()
        .flat_map(|p| [p].into_iter().chain(nested_places(p, body)))
    }

    fn places_written_to(&self) -> impl Iterator<Item = Place> + '_ {
        match self {
            Instruction::Assign(target, _) | Instruction::NewAdt(target, _, _) => Left([*target]),
            Instruction::Assertion(_, _)
            | Instruction::PlaceMention(_)
            | Instruction::Folding(_) => Right([]),
        }
        .into_iter()
    }
}

fn nested_places(p: Place, body: &Body) -> impl Iterator<Item = Place> + '_ {
    body[p.projection].iter().filter_map(|&pj| match pj {
        Projection::Field(_, _) => None,
        Projection::Index(s, _) => Some(s.into()),
    })
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
