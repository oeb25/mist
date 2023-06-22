use std::fmt;

use itertools::{
    Either::{Left, Right},
    Itertools,
};
use la_arena::{Arena, ArenaMap};
use tracing::debug;

use crate::{
    hir::Quantifier,
    mir::{self, SlotId},
    mono::{types::Type, Item},
    util::IdxArena,
};

use super::{Operand, SwitchTargets};

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
    pub fn actions(&self) -> impl Iterator<Item = mir::Action> + '_ {
        self.instructions
            .iter()
            .copied()
            .map(mir::Action::Instruction)
            .chain(self.terminator.map(mir::Action::Terminator))
    }
    pub fn actions_rev(&self) -> impl Iterator<Item = mir::Action> + '_ {
        self.terminator
            .map(mir::Action::Terminator)
            .into_iter()
            .chain(self.instructions.iter().copied().map(mir::Action::Instruction))
    }

    pub fn instructions(&self) -> &[mir::InstructionId] {
        self.instructions.as_ref()
    }

    pub fn terminator(&self) -> Option<mir::Terminator> {
        self.terminator
    }

    pub(crate) fn set_terminator(&mut self, term: mir::Terminator) -> Option<mir::Terminator> {
        let old = self.terminator.replace(term);
        if let Some(_old) = &old {
            debug!("terminator was replaced!");
        }
        old
    }

    pub fn first_loc(&self) -> mir::BlockLocation {
        self.locations().next().unwrap_or(mir::BlockLocation::Terminator(()))
    }

    pub fn locations(&self) -> impl Iterator<Item = mir::BlockLocation> + '_ {
        self.actions().map(|act| act.loc())
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
    pub fn returns(db: &dyn crate::Db) -> mir::Terminator {
        mir::Terminator::new(db, mir::TerminatorKind::Return)
    }
    pub fn goto(db: &dyn crate::Db, bid: mir::BlockId) -> mir::Terminator {
        mir::Terminator::new(db, mir::TerminatorKind::Goto(bid))
    }
    pub fn switch(db: &dyn crate::Db, op: Operand, targets: SwitchTargets) -> mir::Terminator {
        mir::Terminator::new(db, mir::TerminatorKind::Switch(op, targets))
    }
    pub fn quantify(
        db: &dyn crate::Db,
        quantifier: Quantifier,
        vars: Vec<SlotId>,
        bid: mir::BlockId,
    ) -> mir::Terminator {
        mir::Terminator::new(db, mir::TerminatorKind::Quantify(quantifier, vars, bid))
    }
    pub fn quantify_end(db: &dyn crate::Db, bid: mir::BlockId) -> mir::Terminator {
        mir::Terminator::new(db, mir::TerminatorKind::QuantifyEnd(bid))
    }
    pub fn targets(self, db: &dyn crate::Db) -> Vec<mir::BlockId> {
        match self.kind(db) {
            mir::TerminatorKind::Return => vec![],
            mir::TerminatorKind::Goto(b) => vec![*b],
            mir::TerminatorKind::Quantify(_, _, b) => vec![*b],
            mir::TerminatorKind::QuantifyEnd(b) => vec![*b],
            mir::TerminatorKind::Switch(_, switch) => {
                switch.targets.values().copied().chain([switch.otherwise]).collect()
            }
            mir::TerminatorKind::Call { target, .. } => target.iter().copied().collect(),
        }
    }
    pub fn map_targets(
        self,
        db: &dyn crate::Db,
        mut f: impl FnMut(mir::BlockId) -> mir::BlockId,
    ) -> mir::Terminator {
        let mut new = self.kind(db).clone();
        match &mut new {
            mir::TerminatorKind::Return => {}
            mir::TerminatorKind::Goto(b)
            | mir::TerminatorKind::Quantify(_, _, b)
            | mir::TerminatorKind::QuantifyEnd(b) => *b = f(*b),
            mir::TerminatorKind::Switch(_, switch) => {
                for (_, t) in switch.targets.iter_mut() {
                    *t = f(*t);
                }
                switch.otherwise = f(switch.otherwise)
            }
            mir::TerminatorKind::Call { target, .. } => {
                if let Some(b) = target {
                    *b = f(*b)
                }
            }
        };
        mir::Terminator::new(db, new)
    }

    pub fn places_referenced(self, db: &dyn crate::Db) -> impl Iterator<Item = mir::Place> + '_ {
        match self.kind(db) {
            mir::TerminatorKind::Return
            | mir::TerminatorKind::Goto(_)
            | mir::TerminatorKind::Quantify(_, _, _)
            | mir::TerminatorKind::QuantifyEnd(_) => Left(None.into_iter()),
            mir::TerminatorKind::Switch(op, _) => Left(op.place().into_iter()),
            mir::TerminatorKind::Call { args, .. } => {
                Right(args.iter().filter_map(|arg| arg.place()))
            }
        }
        .flat_map(|p| [p].into_iter().chain(p.nested_places(db)))
    }

    pub fn places_written_to(self, db: &dyn crate::Db) -> impl Iterator<Item = mir::Place> + '_ {
        match self.kind(db) {
            mir::TerminatorKind::Call { destination, .. } => Left([*destination].into_iter()),
            mir::TerminatorKind::Return
            | mir::TerminatorKind::Goto(_)
            | mir::TerminatorKind::Quantify(_, _, _)
            | mir::TerminatorKind::QuantifyEnd(_)
            | mir::TerminatorKind::Switch(_, _) => Right([].into_iter()),
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

    pub fn exit_blocks<'a>(
        &'a self,
        db: &'a dyn crate::Db,
    ) -> impl Iterator<Item = mir::BlockId> + 'a {
        self.blocks.iter().filter_map(|(bid, b)| match &b.terminator {
            Some(t) => t.targets(db).is_empty().then_some(bid),
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
    pub fn reference_to<'a>(
        &'a self,
        db: &'a dyn crate::Db,
        x: mir::SlotId,
    ) -> impl Iterator<Item = mir::Action> + 'a {
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
            .map(mir::Action::Instruction)
            .chain(
                self.blocks
                    .iter()
                    .filter_map(move |(_, b)| {
                        let term = b.terminator()?;
                        match term.kind(db) {
                            mir::TerminatorKind::Quantify(_, over, _) => {
                                over.contains(&x).then_some(term)
                            }
                            mir::TerminatorKind::Switch(op, _) => {
                                (Some(x) == op.slot()).then_some(term)
                            }
                            mir::TerminatorKind::Call { args, .. } => {
                                args.iter().any(|arg| Some(x) == arg.slot()).then_some(term)
                            }

                            mir::TerminatorKind::Return
                            | mir::TerminatorKind::Goto(_)
                            | mir::TerminatorKind::QuantifyEnd(_) => None,
                        }
                    })
                    .map_into(),
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

    fn intersperse_block(
        &mut self,
        db: &dyn crate::Db,
        from: mir::BlockId,
        into: mir::BlockId,
        middle: mir::BlockId,
    ) {
        let Some(t) = self.blocks[from].terminator else { return };
        self.blocks[from].terminator =
            Some(t.map_targets(db, |b| if b == into { middle } else { b }));
    }
    pub(crate) fn intersperse_instructions(
        &mut self,
        db: &dyn crate::Db,
        from: mir::BlockId,
        into: mir::BlockId,
        folding: impl Iterator<Item = mir::Instruction>,
    ) {
        let middle = self.blocks.alloc(mir::Block {
            instructions: folding.map(|inst| self.instructions.alloc(inst)).collect(),
            terminator: Some(mir::Terminator::new(db, mir::TerminatorKind::Goto(into))),
        });
        self.intersperse_block(db, from, into, middle);
        // TODO: It might be useful to append to a current block instead of
        // creating a new everytime:

        // match &self.blocks[from].terminator {
        //     Some(term) => match term {
        //         mir::TerminatorKind::Goto(next) => {
        //             assert_eq!(*next, into);
        //             self.blocks[from]
        //                 .instructions
        //                 .extend(folding.map(|inst| self.instructions.alloc(inst)));
        //         }
        //         mir::TerminatorKind::Return => todo!(),
        //         mir::TerminatorKind::Quantify(_, _, _) => todo!(),
        //         mir::TerminatorKind::QuantifyEnd(_) => todo!(),
        //         mir::TerminatorKind::Switch(_, targets) => {
        //             if into == targets.otherwise {
        //             } else {
        //                 for (_, next_bid) in targets.targets.iter_mut() {
        //                     if into == *next_bid {
        //                         let middle = self.blocks.alloc(mir::Block {
        //                             instructions: folding
        //                                 .map(|inst| self.instructions.alloc(inst))
        //                                 .collect(),
        //                             terminator: Some(mir::TerminatorKind::Goto(into)),
        //                         });
        //                         *next_bid = middle;
        //                     }
        //                 }
        //             }
        //         }
        //         mir::TerminatorKind::Call { target, .. } => {
        //             assert_eq!(*target, Some(into));
        //             let middle = self.blocks.alloc(mir::Block {
        //                 instructions: folding.map(|inst| self.instructions.alloc(inst)).collect(),
        //                 terminator: Some(mir::TerminatorKind::Goto(into)),
        //             });
        //             match &mut self.blocks[from].terminator {
        //                 Some(mir::TerminatorKind::Call { target, .. }) => *target = Some(middle),
        //                 _ => unreachable!(),
        //             }
        //         }
        //     },
        //     None => todo!(),
        // }
    }

    pub fn slots_referenced<'a>(
        &'a self,
        db: &'a dyn crate::Db,
        blocks: &'a [mir::BlockId],
    ) -> impl Iterator<Item = mir::SlotId> + 'a {
        blocks.iter().flat_map(|bid| {
            self[*bid].actions().flat_map(|act| act.places_referenced(db, self).map(|p| p.slot()))
        })
    }

    pub fn preceding_blocks<'a>(
        &'a self,
        db: &'a dyn crate::Db,
        bid: mir::BlockId,
    ) -> impl Iterator<Item = mir::BlockId> + 'a {
        self.blocks
            .iter()
            .filter_map(move |(nbid, b)| b.terminator()?.targets(db).contains(&bid).then_some(nbid))
    }
    pub fn succeeding_blocks<'a>(
        &'a self,
        db: &'a dyn crate::Db,
        bid: mir::BlockId,
    ) -> impl Iterator<Item = mir::BlockId> + 'a {
        self.blocks[bid].terminator().into_iter().flat_map(|t| t.targets(db))
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
}

impl mir::Body {
    pub(crate) fn insert_instruction_before(
        &mut self,
        loc: mir::BodyLocation,
        inst: mir::Instruction,
    ) -> mir::InstructionId {
        let id = self.instructions.alloc(inst);
        let b = &mut self.blocks[loc.block];
        let insert_at = loc
            .inner
            .as_instruction()
            .and_then(|inst| b.instructions().iter().position(|&i| i == inst));
        match insert_at {
            Some(insert_idx) => b.instructions.insert(insert_idx, id),
            None => b.instructions.push(id),
        }
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

impl<T> mir::Action<T> {
    pub fn in_block(self, bid: mir::BlockId) -> mir::InBlock<mir::Action<T>> {
        mir::InBlock::new(bid, self)
    }
    pub fn as_instruction(self) -> Option<mir::InstructionId> {
        if let Self::Instruction(v) = self {
            Some(v)
        } else {
            None
        }
    }
    pub(crate) fn map<S>(self, mut f: impl FnMut(T) -> S) -> mir::Action<S> {
        match self {
            mir::Action::Instruction(inst) => mir::Action::Instruction(inst),
            mir::Action::Terminator(t) => mir::Action::Terminator(f(t)),
        }
    }
}
impl mir::Action {
    pub(crate) fn loc(self) -> mir::BlockLocation {
        self.map(|_| ())
    }

    pub(crate) fn places_written_to<'a>(
        self,
        db: &'a dyn crate::Db,
        body: &'a mir::Body,
    ) -> impl Iterator<Item = mir::Place> + 'a {
        match self {
            mir::Action::Instruction(inst) => Left(body[inst].places_written_to()),
            mir::Action::Terminator(t) => Right(t.places_written_to(db)),
        }
    }

    pub(crate) fn places_referenced<'a>(
        self,
        db: &'a dyn crate::Db,
        body: &'a mir::Body,
    ) -> impl Iterator<Item = mir::Place> + 'a {
        match self {
            mir::Action::Instruction(inst) => Left(body[inst].places_referenced(db)),
            mir::Action::Terminator(t) => Right(t.places_referenced(db)),
        }
    }
}

impl<T> mir::InBlock<T> {
    pub fn map<S>(self, mut f: impl FnMut(T) -> S) -> mir::InBlock<S> {
        mir::InBlock::new(self.block, f(self.inner))
    }
}

impl mir::BodyLocation {
    pub fn terminator_of(bid: mir::BlockId) -> mir::BodyLocation {
        mir::BodyLocation::new(bid, mir::Action::Terminator(()))
    }
}

impl mir::InBlock<mir::Action> {
    pub fn loc(self) -> mir::BodyLocation {
        self.map(|f| f.loc())
    }
}
