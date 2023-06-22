use std::fmt;

use itertools::Either::{self, Left, Right};
use la_arena::{Arena, ArenaMap};
use tracing::debug;

use crate::{
    mir,
    mono::{types::Type, Item},
    util::IdxArena,
};

impl mir::MExpr {
    pub fn all_slot_usages(&self) -> impl IntoIterator<Item = mir::SlotId> + '_ {
        match self {
            mir::MExpr::Use(s) => s.slot().into_iter().collect(),
            mir::MExpr::BinaryOp(_, l, r) => l.slot().into_iter().chain(r.slot()).collect(),
            mir::MExpr::Ref(_, p) => vec![p.slot()],
            mir::MExpr::UnaryOp(_, o) => o.slot().into_iter().collect(),
        }
    }
    pub fn all_operands(&self) -> impl IntoIterator<Item = &mir::Operand> {
        match self {
            mir::MExpr::Use(s) => vec![s],
            mir::MExpr::BinaryOp(_, l, r) => vec![l, r],
            mir::MExpr::Ref(_, _) => vec![],
            mir::MExpr::UnaryOp(_, o) => vec![o],
        }
    }
    pub fn places(&self) -> impl Iterator<Item = mir::Place> + '_ {
        self.all_operands().into_iter().filter_map(|o| o.place())
    }
}

impl mir::Folding {
    pub fn place(self) -> mir::Place {
        match self {
            mir::Folding::Fold { into } => into,
            mir::Folding::Unfold { consume } => consume,
        }
    }
}

impl mir::MExpr {
    #[allow(dead_code)]
    fn map_operand(&self, mut map: impl FnMut(&mir::Operand) -> mir::Operand) -> mir::MExpr {
        match self {
            mir::MExpr::Use(o) => mir::MExpr::Use(map(o)),
            mir::MExpr::Ref(bk, o) => mir::MExpr::Ref(*bk, *o),
            mir::MExpr::BinaryOp(op, l, r) => mir::MExpr::BinaryOp(*op, map(l), map(r)),
            mir::MExpr::UnaryOp(op, o) => mir::MExpr::UnaryOp(*op, map(o)),
        }
    }
}

impl mir::Block {
    pub fn instructions(&self) -> &[mir::InstructionId] {
        self.instructions.as_ref()
    }

    pub fn terminator(&self) -> Option<&mir::Terminator> {
        self.terminator.as_ref()
    }

    pub(crate) fn set_terminator(&mut self, term: mir::Terminator) -> Option<mir::Terminator> {
        let old = self.terminator.replace(term);
        if let Some(_old) = &old {
            debug!("terminator was replaced!");
        }
        old
    }

    pub fn first_loc(&self) -> mir::BlockLocation {
        self.instructions
            .iter()
            .copied()
            .map(mir::BlockLocation::Instruction)
            .next()
            .unwrap_or(mir::BlockLocation::Terminator)
    }

    pub fn locations(&self) -> impl Iterator<Item = mir::BlockLocation> + '_ {
        self.instructions
            .iter()
            .copied()
            .map(mir::BlockLocation::Instruction)
            .chain(self.terminator.is_some().then_some(mir::BlockLocation::Terminator))
    }
}

impl mir::SwitchTargets {
    pub(crate) fn new<const N: usize>(
        success: [(u128, mir::BlockId); N],
        otherwise: mir::BlockId,
    ) -> mir::SwitchTargets {
        let mut values = Arena::default();
        let mut targets = ArenaMap::default();
        for (v, bid) in success {
            targets.insert(values.alloc(v), bid);
        }

        mir::SwitchTargets { values, targets, otherwise }
    }
    pub fn values(&self) -> (impl Iterator<Item = (u128, mir::BlockId)> + '_, mir::BlockId) {
        (self.targets.iter().map(|(v, t)| (self.values[v], *t)), self.otherwise)
    }
    pub fn targets(&self) -> (impl Iterator<Item = mir::BlockId> + '_, mir::BlockId) {
        (self.targets.iter().map(|(_, b)| *b), self.otherwise)
    }

    pub fn has_values(&self) -> bool {
        !self.values.is_empty()
    }
}

impl mir::Terminator {
    /// If this replaces an existing target, that target is returned
    pub fn set_target(&mut self, bid: mir::BlockId) -> Option<mir::BlockId> {
        match self {
            mir::Terminator::Return => None,
            mir::Terminator::Goto(t) => Some(std::mem::replace(t, bid)),
            mir::Terminator::Quantify(_, _, t) => Some(std::mem::replace(t, bid)),
            mir::Terminator::QuantifyEnd(t) => Some(std::mem::replace(t, bid)),
            mir::Terminator::Switch(_, _) => {
                // TODO
                None
            }
            mir::Terminator::Call { target, .. } => std::mem::replace(target, Some(bid)),
        }
    }
    pub fn targets(&self) -> Vec<mir::BlockId> {
        match self {
            mir::Terminator::Return => vec![],
            mir::Terminator::Goto(b) => vec![*b],
            mir::Terminator::Quantify(_, _, b) => vec![*b],
            mir::Terminator::QuantifyEnd(b) => vec![*b],
            mir::Terminator::Switch(_, switch) => {
                switch.targets.values().copied().chain([switch.otherwise]).collect()
            }
            mir::Terminator::Call { target, .. } => target.iter().copied().collect(),
        }
    }
    pub fn map_targets_mut(&mut self, mut f: impl FnMut(mir::BlockId) -> mir::BlockId) {
        match self {
            mir::Terminator::Return => {}
            mir::Terminator::Goto(b)
            | mir::Terminator::Quantify(_, _, b)
            | mir::Terminator::QuantifyEnd(b) => *b = f(*b),
            mir::Terminator::Switch(_, switch) => {
                for (_, t) in switch.targets.iter_mut() {
                    *t = f(*t);
                }
                switch.otherwise = f(switch.otherwise)
            }
            mir::Terminator::Call { target, .. } => {
                if let Some(b) = target {
                    *b = f(*b)
                }
            }
        }
    }

    pub fn places_referenced<'a>(
        &'a self,
        db: &'a dyn crate::Db,
    ) -> impl Iterator<Item = mir::Place> + 'a {
        match self {
            mir::Terminator::Return
            | mir::Terminator::Goto(_)
            | mir::Terminator::Quantify(_, _, _)
            | mir::Terminator::QuantifyEnd(_) => Left(None.into_iter()),
            mir::Terminator::Switch(op, _) => Left(op.place().into_iter()),
            mir::Terminator::Call { args, .. } => Right(args.iter().filter_map(|arg| arg.place())),
        }
        .flat_map(|p| [p].into_iter().chain(p.nested_places(db)))
    }

    pub fn places_written_to(&self) -> impl Iterator<Item = mir::Place> + '_ {
        match self {
            mir::Terminator::Call { destination, .. } => Left([*destination].into_iter()),
            mir::Terminator::Return
            | mir::Terminator::Goto(_)
            | mir::Terminator::Quantify(_, _, _)
            | mir::Terminator::QuantifyEnd(_)
            | mir::Terminator::Switch(_, _) => Right([].into_iter()),
        }
    }

    fn places(&self) -> impl Iterator<Item = mir::Place> + '_ {
        match self {
            mir::Terminator::Return
            | mir::Terminator::Goto(_)
            | mir::Terminator::Quantify(_, _, _)
            | mir::Terminator::QuantifyEnd(_) => Left(None.into_iter()),
            mir::Terminator::Switch(op, _) => Left(op.place().into_iter()),
            mir::Terminator::Call { args, destination, .. } => {
                Right(args.iter().filter_map(|arg| arg.place()).chain([*destination]))
            }
        }
    }
}

impl mir::Body {
    pub(crate) fn new(item: Item) -> mir::Body {
        let mut slots: IdxArena<_> = Default::default();
        let self_slot = slots.alloc(mir::Slot::Self_);

        mir::Body {
            item,

            self_slot,

            blocks: Default::default(),
            instructions: Default::default(),
            slots,

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

    pub fn result_slot(&self) -> Option<mir::SlotId> {
        self.result_slot
    }
    pub fn self_slot(&self) -> mir::SlotId {
        self.self_slot
    }

    pub fn entry_blocks(&self) -> impl Iterator<Item = mir::BlockId> + '_ {
        itertools::chain!(
            itertools::chain!(self.requires(), self.invariants(), self.ensures()).copied(),
            self.body_block(),
            self.block_invariants.iter().flat_map(|(_, invs)| invs).copied()
        )
    }
    pub fn is_requires(&self, bid: mir::BlockId) -> bool {
        self.requires.contains(&bid)
    }
    pub fn is_ensures(&self, bid: mir::BlockId) -> bool {
        self.ensures.contains(&bid)
    }

    pub fn slots(&self) -> impl Iterator<Item = mir::SlotId> + '_ {
        self.slots.idxs()
    }

    pub fn exit_blocks(&self) -> impl Iterator<Item = mir::BlockId> + '_ {
        self.blocks.iter().filter_map(|(bid, b)| match &b.terminator {
            Some(t) => t.targets().is_empty().then_some(bid),
            None => Some(bid),
        })
    }

    pub fn body_block(&self) -> Option<mir::BlockId> {
        self.body_block
    }

    pub fn requires(&self) -> &[mir::BlockId] {
        self.requires.as_ref()
    }

    pub fn ensures(&self) -> &[mir::BlockId] {
        self.ensures.as_ref()
    }

    pub fn invariants(&self) -> &[mir::BlockId] {
        self.invariants.as_ref()
    }

    pub fn assignments_to(&self, x: mir::SlotId) -> impl Iterator<Item = mir::InstructionId> + '_ {
        self.instructions.iter().filter_map(move |(id, inst)| match inst {
            mir::Instruction::Assign(y, _) if x == y.slot() => Some(id),
            _ => None,
        })
    }
    pub fn reference_to(
        &self,
        x: mir::SlotId,
    ) -> impl Iterator<Item = Either<mir::InstructionId, &mir::Terminator>> + '_ {
        self.instructions
            .iter()
            .filter_map(move |(id, inst)| match inst {
                mir::Instruction::Assign(_, e) | mir::Instruction::Assertion(_, e)
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
                            mir::Terminator::Quantify(_, over, _) => {
                                over.contains(&x).then_some(term)
                            }
                            mir::Terminator::Switch(op, _) => {
                                (Some(x) == op.slot()).then_some(term)
                            }
                            mir::Terminator::Call { args, .. } => {
                                args.iter().any(|arg| Some(x) == arg.slot()).then_some(term)
                            }

                            mir::Terminator::Return
                            | mir::Terminator::Goto(_)
                            | mir::Terminator::QuantifyEnd(_) => None,
                        }
                    })
                    .map(Right),
            )
    }

    pub fn params(&self) -> &[mir::SlotId] {
        self.params.as_ref()
    }

    pub fn slot_ty(&self, db: &dyn crate::Db, slot: mir::SlotId) -> Type {
        self.slot_type.get(slot).copied().unwrap_or_else(|| Type::error(db))
    }

    pub fn place_ty(&self, db: &dyn crate::Db, place: mir::Place) -> Type {
        match place.projection(db).last(db) {
            None => self.slot_ty(db, place.slot()),
            Some(mir::Projection::Field(_, ty) | mir::Projection::Index(_, ty)) => ty,
        }
    }

    pub fn def(&self) -> Item {
        self.item
    }

    pub fn block_invariants(&self, block: mir::BlockId) -> &[mir::BlockId] {
        self.block_invariants.get(block).map(|invs| invs.as_slice()).unwrap_or_else(|| &[])
    }

    fn intersperse_block(&mut self, from: mir::BlockId, into: mir::BlockId, middle: mir::BlockId) {
        let Some(t) = &mut self.blocks[from].terminator else { return };
        t.map_targets_mut(|b| if b == into { middle } else { b });
    }
    pub(crate) fn intersperse_instructions(
        &mut self,
        from: mir::BlockId,
        into: mir::BlockId,
        folding: impl Iterator<Item = mir::Instruction>,
    ) {
        let middle = self.blocks.alloc(mir::Block {
            instructions: folding.map(|inst| self.instructions.alloc(inst)).collect(),
            terminator: Some(mir::Terminator::Goto(into)),
        });
        self.intersperse_block(from, into, middle);
        // TODO: It might be useful to append to a current block instead of
        // creating a new everytime:

        // match &self.blocks[from].terminator {
        //     Some(term) => match term {
        //         mir::Terminator::Goto(next) => {
        //             assert_eq!(*next, into);
        //             self.blocks[from]
        //                 .instructions
        //                 .extend(folding.map(|inst| self.instructions.alloc(inst)));
        //         }
        //         mir::Terminator::Return => todo!(),
        //         mir::Terminator::Quantify(_, _, _) => todo!(),
        //         mir::Terminator::QuantifyEnd(_) => todo!(),
        //         mir::Terminator::Switch(_, targets) => {
        //             if into == targets.otherwise {
        //             } else {
        //                 for (_, next_bid) in targets.targets.iter_mut() {
        //                     if into == *next_bid {
        //                         let middle = self.blocks.alloc(mir::Block {
        //                             instructions: folding
        //                                 .map(|inst| self.instructions.alloc(inst))
        //                                 .collect(),
        //                             terminator: Some(mir::Terminator::Goto(into)),
        //                         });
        //                         *next_bid = middle;
        //                     }
        //                 }
        //             }
        //         }
        //         mir::Terminator::Call { target, .. } => {
        //             assert_eq!(*target, Some(into));
        //             let middle = self.blocks.alloc(mir::Block {
        //                 instructions: folding.map(|inst| self.instructions.alloc(inst)).collect(),
        //                 terminator: Some(mir::Terminator::Goto(into)),
        //             });
        //             match &mut self.blocks[from].terminator {
        //                 Some(mir::Terminator::Call { target, .. }) => *target = Some(middle),
        //                 _ => unreachable!(),
        //             }
        //         }
        //     },
        //     None => todo!(),
        // }
    }

    pub fn slots_referenced<'a>(
        &'a self,
        blocks: &'a [mir::BlockId],
    ) -> impl Iterator<Item = mir::SlotId> + 'a {
        blocks.iter().flat_map(|bid| {
            self[*bid]
                .instructions()
                .iter()
                .flat_map(|inst| self[inst].places().map(|p| p.slot()))
                .chain(
                    self[*bid]
                        .terminator()
                        .into_iter()
                        .flat_map(|term| term.places().map(|p| p.slot())),
                )
        })
    }

    pub fn preceding_blocks(&self, bid: mir::BlockId) -> impl Iterator<Item = mir::BlockId> + '_ {
        self.blocks
            .iter()
            .filter_map(move |(nbid, b)| b.terminator()?.targets().contains(&bid).then_some(nbid))
    }
    pub fn succeeding_blocks(&self, bid: mir::BlockId) -> impl Iterator<Item = mir::BlockId> + '_ {
        self.blocks[bid].terminator().into_iter().flat_map(|t| t.targets())
    }

    /// Returns an iterator over everything that local to the body. This
    /// includes `mir::Slot::Temp` and `mir::Slot::Local(..)`.
    pub fn locals(&self) -> impl Iterator<Item = mir::SlotId> + '_ {
        self.slots.iter().filter_map(|(sid, slot)| match slot {
            mir::Slot::Temp | mir::Slot::Local(_) => Some(sid),
            _ => None,
        })
    }

    pub fn first_loc_in(&self, bid: mir::BlockId) -> mir::BodyLocation {
        self[bid].first_loc().in_block(bid)
    }

    pub fn locations_in(&self, bid: mir::BlockId) -> impl Iterator<Item = mir::BodyLocation> + '_ {
        self[bid].locations().map(move |loc| loc.in_block(bid))
    }
}

impl mir::Body {
    pub(crate) fn insert_instruction_before(
        &mut self,
        loc: mir::BodyLocation,
        inst: mir::Instruction,
    ) -> mir::InstructionId {
        let insert_idx = match loc.inner {
            mir::BlockLocation::Instruction(inst) => {
                self[loc.block].instructions().iter().position(|&i| i == inst).unwrap()
            }
            mir::BlockLocation::Terminator => self[loc.block].instructions().len(),
        };
        let id = self.instructions.alloc(inst);
        self.blocks[loc.block].instructions.insert(insert_idx, id);
        id
    }
}

impl std::ops::Index<mir::BlockId> for mir::Body {
    type Output = mir::Block;

    fn index(&self, index: mir::BlockId) -> &Self::Output {
        &self.blocks[index]
    }
}
impl std::ops::Index<&'_ mir::BlockId> for mir::Body {
    type Output = mir::Block;

    fn index(&self, index: &'_ mir::BlockId) -> &Self::Output {
        &self.blocks[*index]
    }
}
impl std::ops::Index<mir::InstructionId> for mir::Body {
    type Output = mir::Instruction;

    fn index(&self, index: mir::InstructionId) -> &Self::Output {
        &self.instructions[index]
    }
}
impl std::ops::Index<&'_ mir::InstructionId> for mir::Body {
    type Output = mir::Instruction;

    fn index(&self, index: &'_ mir::InstructionId) -> &Self::Output {
        &self.instructions[*index]
    }
}
impl std::ops::Index<mir::SlotId> for mir::Body {
    type Output = mir::Slot;

    fn index(&self, index: mir::SlotId) -> &Self::Output {
        &self.slots[index]
    }
}
impl std::ops::Index<&'_ mir::SlotId> for mir::Body {
    type Output = mir::Slot;

    fn index(&self, index: &'_ mir::SlotId) -> &Self::Output {
        &self.slots[*index]
    }
}

impl fmt::Debug for mir::BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ":B{}", self.0.into_raw())
    }
}
impl fmt::Display for mir::BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ":B{}", self.0.into_raw())
    }
}

impl mir::BlockLocation {
    pub fn in_block(self, bid: mir::BlockId) -> mir::BodyLocation {
        mir::BodyLocation { block: bid, inner: self }
    }

    pub fn as_instruction(self) -> Option<mir::InstructionId> {
        if let Self::Instruction(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl mir::Instruction {
    pub fn places(&self) -> impl Iterator<Item = mir::Place> + '_ {
        match self {
            mir::Instruction::Assign(target, expr) => {
                Left(Left([*target].into_iter().chain(Left(expr.places()))))
            }
            mir::Instruction::NewAdt(target, _, fields) => Left(Left(
                [*target].into_iter().chain(Right(fields.iter().flat_map(|f| f.1.place()))),
            )),
            mir::Instruction::Assertion(_, expr) => Left(Right(expr.places())),
            mir::Instruction::PlaceMention(p) => Right([*p].into_iter()),
            mir::Instruction::Folding(folding) => match folding {
                mir::Folding::Fold { into } => Right([*into].into_iter()),
                mir::Folding::Unfold { consume } => Right([*consume].into_iter()),
            },
        }
    }

    pub fn places_referenced<'a>(
        &'a self,
        db: &'a dyn crate::Db,
    ) -> impl Iterator<Item = mir::Place> + 'a {
        match self {
            mir::Instruction::Assign(_, expr) => {
                // TODO: Perhaps the targets parent should be part of the
                // referenced as well?
                Left(None.into_iter().chain(Left(expr.places())))
            }
            mir::Instruction::NewAdt(_, _, fields) => {
                Left(None.into_iter().chain(Right(fields.iter().flat_map(|f| f.1.place()))))
            }
            mir::Instruction::Assertion(_, expr) => {
                Left(None.into_iter().chain(Left(expr.places())))
            }
            mir::Instruction::PlaceMention(p) => Right([*p]),
            mir::Instruction::Folding(folding) => match *folding {
                mir::Folding::Fold { into } => Right([into]),
                mir::Folding::Unfold { consume } => Right([consume]),
            },
        }
        .into_iter()
        .flat_map(|p| [p].into_iter().chain(p.nested_places(db)))
    }

    pub fn places_written_to(&self) -> impl Iterator<Item = mir::Place> + '_ {
        match self {
            mir::Instruction::Assign(target, _) | mir::Instruction::NewAdt(target, _, _) => {
                Left([*target])
            }
            mir::Instruction::Assertion(_, _)
            | mir::Instruction::PlaceMention(_)
            | mir::Instruction::Folding(_) => Right([]),
        }
        .into_iter()
    }
}

impl mir::Operand {
    pub fn place(&self) -> Option<mir::Place> {
        match self {
            mir::Operand::Copy(s) | mir::Operand::Move(s) => Some(*s),
            mir::Operand::Literal(_) => None,
        }
    }
    pub fn slot(&self) -> Option<mir::SlotId> {
        self.place().map(|s| s.slot())
    }
}
