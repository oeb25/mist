use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
};

use crate::{
    mir,
    util::{IdxMap, IdxSet, IdxWrap},
};

pub struct AnalysisResults<A: MonotoneFramework> {
    facts: IdxMap<mir::BlockId, A::Domain>,
    semantic_calls: usize,
}

impl<A: MonotoneFramework> fmt::Debug for AnalysisResults<A>
where
    A::Domain: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AnalysisResults")
            .field("facts", &self.facts)
            .field("semantic_calls", &self.semantic_calls)
            .finish()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Progress {
    No,
    Yes,
}

pub trait Direction {
    fn initial_blocks(body: &mir::Body, f: impl FnMut(mir::BlockId));
    fn semantic<A: MonotoneFramework>(
        a: &A,
        body: &mir::Body,
        facts: &mut IdxMap<mir::BlockId, A::Domain>,
        bid: mir::BlockId,
    ) -> Progress;
    fn next(body: &mir::Body, bid: mir::BlockId, f: impl FnMut(mir::BlockId));
}

pub struct Forward;
pub struct Backward;

impl Direction for Forward {
    fn initial_blocks(body: &mir::Body, mut f: impl FnMut(mir::BlockId)) {
        for bid in body.entry_blocks() {
            f(bid);
        }
    }

    fn semantic<A: MonotoneFramework>(
        a: &A,
        body: &mir::Body,
        facts: &mut IdxMap<mir::BlockId, A::Domain>,
        bid: mir::BlockId,
    ) -> Progress {
        let mut progress = Progress::No;

        for d in body.preceding_blocks(bid) {
            let mut prev = facts[d].clone();
            for &inst in body[d].instructions() {
                a.instruction_semantic(body, inst, &mut prev);
            }
            if let Some(term) = body[d].terminator() {
                a.terminator_semantic(body, term, &mut prev);
            }
            if !facts[bid].contains(&prev) {
                progress = Progress::Yes;
                facts[bid].lub_extend(&prev);
            }
        }

        progress
    }

    fn next(body: &mir::Body, bid: mir::BlockId, mut f: impl FnMut(mir::BlockId)) {
        for b in body.succeeding_blocks(bid) {
            f(b);
        }
    }
}
impl Direction for Backward {
    fn initial_blocks(body: &mir::Body, mut f: impl FnMut(mir::BlockId)) {
        for bid in body.exit_blocks() {
            f(bid);
        }
    }

    fn semantic<A: MonotoneFramework>(
        a: &A,
        body: &mir::Body,
        facts: &mut IdxMap<mir::BlockId, A::Domain>,
        bid: mir::BlockId,
    ) -> Progress {
        let mut progress = Progress::No;

        for d in body.succeeding_blocks(bid) {
            let mut prev = facts[d].clone();
            if let Some(term) = body[d].terminator() {
                a.terminator_semantic(body, term, &mut prev);
            }
            for &inst in body[d].instructions().iter().rev() {
                a.instruction_semantic(body, inst, &mut prev);
            }
            if !facts[bid].contains(&prev) {
                progress = Progress::Yes;
                facts[bid].lub_extend(&prev);
            }
        }

        progress
    }

    fn next(body: &mir::Body, bid: mir::BlockId, mut f: impl FnMut(mir::BlockId)) {
        for b in body.succeeding_blocks(bid) {
            f(b);
        }
    }
}

pub trait MonotoneFramework {
    type Domain: Lattice;
    type Direction: Direction;
    fn instruction_semantic(
        &self,
        body: &mir::Body,
        inst: mir::InstructionId,
        prev: &mut Self::Domain,
    );
    fn terminator_semantic(
        &self,
        body: &mir::Body,
        terminator: &mir::Terminator,
        prev: &mut Self::Domain,
    );
    fn initial(&self, body: &mir::Body) -> Self::Domain;
    fn debug(&self, item: &Self::Domain) {
        let _ = item;
    }
}

pub trait Lattice: Sized + Clone {
    fn bottom() -> Self;
    fn lub_extend(&mut self, other: &Self) {
        *self = self.lub(other);
    }
    fn lub(&self, other: &Self) -> Self;
    fn contains(&self, other: &Self) -> bool;
}

pub trait Worklist {
    fn empty() -> Self;
    fn insert(&mut self, b: mir::BlockId);
    fn extract(&mut self) -> Option<mir::BlockId>;
}

pub struct FiFo(VecDeque<mir::BlockId>);
impl Worklist for FiFo {
    fn empty() -> Self {
        FiFo(Default::default())
    }

    fn insert(&mut self, n: mir::BlockId) {
        self.0.push_back(n)
    }

    fn extract(&mut self) -> Option<mir::BlockId> {
        self.0.pop_front()
    }
}

pub struct LiFo(Vec<mir::BlockId>);
impl Worklist for LiFo {
    fn empty() -> Self {
        LiFo(Default::default())
    }

    fn insert(&mut self, n: mir::BlockId) {
        self.0.push(n);
    }

    fn extract(&mut self) -> Option<mir::BlockId> {
        self.0.pop()
    }
}

pub fn mono_analysis<A: MonotoneFramework, W: Worklist>(
    a: A,
    body: &mir::Body,
) -> AnalysisResults<A> {
    let mut worklist = W::empty();

    let bot = A::Domain::bottom();

    let mut facts: IdxMap<mir::BlockId, A::Domain> = IdxMap::default();
    for (bid, _) in body.blocks.iter() {
        facts.insert(bid, bot.clone());
        worklist.insert(bid);
    }

    let initial = a.initial(body);
    A::Direction::initial_blocks(body, |bid| {
        facts.insert(bid, initial.clone());
    });

    let mut calls = 0;

    while let Some(n) = worklist.extract() {
        calls += 1;

        match A::Direction::semantic(&a, body, &mut facts, n) {
            Progress::No => {}
            Progress::Yes => {
                A::Direction::next(body, n, |b| worklist.insert(b));
            }
        }
    }

    AnalysisResults {
        facts,
        semantic_calls: calls,
    }
}

impl<A> AnalysisResults<A>
where
    A: MonotoneFramework,
{
    pub fn entry(&self, bid: mir::BlockId) -> &A::Domain
    where
        A: MonotoneFramework<Direction = Backward>,
    {
        &self.facts[bid]
    }
    pub fn exit(&self, bid: mir::BlockId) -> &A::Domain
    where
        A: MonotoneFramework<Direction = Forward>,
    {
        &self.facts[bid]
    }
}

impl Lattice for () {
    fn bottom() -> Self {}

    fn lub(&self, _other: &Self) -> Self {}

    fn contains(&self, _other: &Self) -> bool {
        true
    }
}

impl<T> Lattice for HashSet<T>
where
    T: std::hash::Hash + PartialEq + Eq + Clone,
{
    fn bottom() -> Self {
        Self::default()
    }

    fn lub_extend(&mut self, other: &Self) {
        self.extend(other.iter().cloned());
    }

    fn lub(&self, other: &Self) -> Self {
        self.union(other).cloned().collect()
    }

    fn contains(&self, other: &Self) -> bool {
        other.is_subset(self)
    }
}

impl<K, V> Lattice for HashMap<K, V>
where
    K: std::hash::Hash + PartialEq + Eq + Clone,
    V: Lattice + Clone,
{
    fn bottom() -> Self {
        Self::default()
    }

    fn lub_extend(&mut self, other: &Self) {
        for (k, b) in other {
            if let Some(a) = self.get_mut(k) {
                a.lub_extend(b);
            } else {
                self.insert(k.clone(), b.clone());
            }
        }
    }

    fn lub(&self, other: &Self) -> Self {
        let mut result = Self::default();

        for (k, a) in self {
            if let Some(b) = other.get(k) {
                result.insert(k.clone(), a.lub(b));
            } else {
                result.insert(k.clone(), a.clone());
            }
        }
        for (k, b) in other {
            if !self.contains_key(k) {
                result.insert(k.clone(), b.clone());
            }
        }

        result
    }

    fn contains(&self, other: &Self) -> bool {
        other.iter().all(|(k, a)| {
            if let Some(b) = self.get(k) {
                b.contains(a)
            } else {
                false
            }
        })
    }
}

impl<K, V> Lattice for IdxMap<K, V>
where
    K: IdxWrap,
    V: Lattice + Clone,
{
    fn bottom() -> Self {
        Self::default()
    }

    fn lub_extend(&mut self, other: &Self) {
        for (k, b) in other.iter() {
            if let Some(a) = self.get_mut(k) {
                a.lub_extend(b);
            } else {
                self.insert(k, b.clone());
            }
        }
    }

    fn lub(&self, other: &Self) -> Self {
        let mut result = Self::default();

        for (k, a) in self.iter() {
            if let Some(b) = other.get(k) {
                result.insert(k, a.lub(b));
            } else {
                result.insert(k, a.clone());
            }
        }
        for (k, b) in other.iter() {
            if !self.contains_idx(k) {
                result.insert(k, b.clone());
            }
        }

        result
    }

    fn contains(&self, other: &Self) -> bool {
        other.iter().all(|(k, a)| {
            if let Some(b) = self.get(k) {
                b.contains(a)
            } else {
                false
            }
        })
    }
}

impl<K: IdxWrap> Lattice for IdxSet<K> {
    fn bottom() -> Self {
        Self::default()
    }

    fn lub_extend(&mut self, other: &Self) {
        for k in other.iter() {
            self.insert(k);
        }
    }

    fn lub(&self, other: &Self) -> Self {
        let mut result = Self::default();

        for k in self.iter() {
            result.insert(k);
        }
        for k in other.iter() {
            result.insert(k);
        }

        result
    }

    fn contains(&self, other: &Self) -> bool {
        other.iter().all(|k| self.contains_idx(k))
    }
}
