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
        prev: &mut A::Domain,
        bid: mir::BlockId,
    );
    fn semantics<A: MonotoneFramework>(
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
        prev: &mut A::Domain,
        bid: mir::BlockId,
    ) {
        for &inst in body[bid].instructions() {
            a.instruction_semantic(body, inst, prev);
        }
        if let Some(term) = body[bid].terminator() {
            a.terminator_semantic(body, term, prev);
        }
    }

    fn semantics<A: MonotoneFramework>(
        a: &A,
        body: &mir::Body,
        facts: &mut IdxMap<mir::BlockId, A::Domain>,
        bid: mir::BlockId,
    ) -> Progress {
        let mut progress = Progress::No;

        for d in body.preceding_blocks(bid) {
            let mut prev = facts[d].clone();
            Self::semantic(a, body, &mut prev, bid);
            if !facts[bid].contains(body, &prev) {
                progress = Progress::Yes;
                facts[bid].lub_extend(body, &prev);
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
        prev: &mut A::Domain,
        bid: mir::BlockId,
    ) {
        if let Some(term) = body[bid].terminator() {
            a.terminator_semantic(body, term, prev);
        }
        for &inst in body[bid].instructions().iter().rev() {
            a.instruction_semantic(body, inst, prev);
        }
    }

    fn semantics<A: MonotoneFramework>(
        a: &A,
        body: &mir::Body,
        facts: &mut IdxMap<mir::BlockId, A::Domain>,
        bid: mir::BlockId,
    ) -> Progress {
        let mut progress = Progress::No;

        for d in body.succeeding_blocks(bid) {
            let mut prev = facts[d].clone();
            Self::semantic(a, body, &mut prev, bid);
            if !facts[bid].contains(body, &prev) {
                progress = Progress::Yes;
                facts[bid].lub_extend(body, &prev);
            }
        }

        progress
    }

    fn next(body: &mir::Body, bid: mir::BlockId, mut f: impl FnMut(mir::BlockId)) {
        for b in body.preceding_blocks(bid) {
            f(b);
        }
    }
}

pub trait MonotoneFramework {
    type Domain: Lattice<mir::Body> + fmt::Debug;
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

pub trait Lattice<Ctx>: Sized + Clone {
    fn bottom(ctx: &Ctx) -> Self;
    fn lub_extend(&mut self, ctx: &Ctx, other: &Self) {
        *self = self.lub(ctx, other);
    }
    fn lub(&self, _ctx: &Ctx, other: &Self) -> Self;
    fn contains(&self, _ctx: &Ctx, other: &Self) -> bool;
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

    let bot = A::Domain::bottom(body);

    let mut facts: IdxMap<mir::BlockId, A::Domain> = IdxMap::default();
    for (bid, _) in body.blocks.iter() {
        facts.insert(bid, bot.clone());
        worklist.insert(bid);
    }

    let initial = a.initial(body);
    A::Direction::initial_blocks(body, |bid| {
        let mut prev = initial.clone();
        A::Direction::semantic(&a, body, &mut prev, bid);
        facts.insert(bid, prev);
    });

    let mut calls = 0;

    while let Some(n) = worklist.extract() {
        calls += 1;

        match A::Direction::semantics(&a, body, &mut facts, n) {
            Progress::No => {}
            Progress::Yes => A::Direction::next(body, n, |b| worklist.insert(b)),
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
        self.value_at(bid)
    }
    pub fn exit(&self, bid: mir::BlockId) -> &A::Domain
    where
        A: MonotoneFramework<Direction = Forward>,
    {
        self.value_at(bid)
    }
    /// Returns the value computed as the given block. Depending on the
    /// direction of the analysis, the value will be placed differently on the
    /// graph:
    /// - [`Forward`]: value at **exit** of the node is returned,
    /// - [`Backward`]: value to **entry** of the node is returned.
    pub fn value_at(&self, bid: mir::BlockId) -> &A::Domain {
        &self.facts[bid]
    }
}

impl<Ctx> Lattice<Ctx> for () {
    fn bottom(_ctx: &Ctx) -> Self {}

    fn lub(&self, _ctx: &Ctx, _other: &Self) -> Self {}

    fn contains(&self, _ctx: &Ctx, _other: &Self) -> bool {
        true
    }
}

impl<Ctx, T> Lattice<Ctx> for HashSet<T>
where
    T: std::hash::Hash + PartialEq + Eq + Clone,
{
    fn bottom(_ctx: &Ctx) -> Self {
        Self::default()
    }

    fn lub_extend(&mut self, _ctx: &Ctx, other: &Self) {
        self.extend(other.iter().cloned());
    }

    fn lub(&self, _ctx: &Ctx, other: &Self) -> Self {
        self.union(other).cloned().collect()
    }

    fn contains(&self, _ctx: &Ctx, other: &Self) -> bool {
        self.is_superset(other)
    }
}

impl<Ctx, K, V> Lattice<Ctx> for HashMap<K, V>
where
    K: std::hash::Hash + PartialEq + Eq + Clone,
    V: Lattice<Ctx> + Clone,
{
    fn bottom(_ctx: &Ctx) -> Self {
        Self::default()
    }

    fn lub_extend(&mut self, ctx: &Ctx, other: &Self) {
        for (k, b) in other {
            if let Some(a) = self.get_mut(k) {
                a.lub_extend(ctx, b);
            } else {
                self.insert(k.clone(), b.clone());
            }
        }
    }

    fn lub(&self, ctx: &Ctx, other: &Self) -> Self {
        let mut result = Self::default();

        for (k, a) in self {
            if let Some(b) = other.get(k) {
                result.insert(k.clone(), a.lub(ctx, b));
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

    fn contains(&self, ctx: &Ctx, other: &Self) -> bool {
        other.iter().all(|(k, a)| {
            if let Some(b) = self.get(k) {
                b.contains(ctx, a)
            } else {
                false
            }
        })
    }
}

impl<Ctx, K, V> Lattice<Ctx> for IdxMap<K, V>
where
    K: IdxWrap,
    V: Lattice<Ctx> + Clone,
{
    fn bottom(_ctx: &Ctx) -> Self {
        Self::default()
    }

    fn lub_extend(&mut self, ctx: &Ctx, other: &Self) {
        for (k, b) in other.iter() {
            if let Some(a) = self.get_mut(k) {
                a.lub_extend(ctx, b);
            } else {
                self.insert(k, b.clone());
            }
        }
    }

    fn lub(&self, ctx: &Ctx, other: &Self) -> Self {
        let mut result = Self::default();

        for (k, a) in self.iter() {
            if let Some(b) = other.get(k) {
                result.insert(k, a.lub(ctx, b));
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

    fn contains(&self, ctx: &Ctx, other: &Self) -> bool {
        other.iter().all(|(k, a)| {
            if let Some(b) = self.get(k) {
                b.contains(ctx, a)
            } else {
                false
            }
        })
    }
}

impl<Ctx, K: IdxWrap> Lattice<Ctx> for IdxSet<K> {
    fn bottom(_ctx: &Ctx) -> Self {
        Self::default()
    }

    fn lub_extend(&mut self, _ctx: &Ctx, other: &Self) {
        for k in other.iter() {
            self.insert(k);
        }
    }

    fn lub(&self, _ctx: &Ctx, other: &Self) -> Self {
        let mut result = Self::default();

        for k in self.iter() {
            result.insert(k);
        }
        for k in other.iter() {
            result.insert(k);
        }

        result
    }

    fn contains(&self, _ctx: &Ctx, other: &Self) -> bool {
        other.iter().all(|k| self.contains_idx(k))
    }
}
