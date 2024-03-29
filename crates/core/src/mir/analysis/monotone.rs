use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
};

use crate::{
    mir,
    util::{IdxMap, IdxSet, IdxWrap},
};

pub struct AnalysisResults<A: MonotoneFramework> {
    facts: HashMap<mir::BodyLocation, A::Domain>,
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
    fn initial_blocks(db: &dyn crate::Db, ib: &mir::ItemBody, f: impl FnMut(mir::BlockId));
    fn semantic<A: MonotoneFramework>(
        db: &dyn crate::Db,
        a: &A,
        body: &mir::Body,
        prev: &mut A::Domain,
        bid: mir::BlockId,
        events: impl for<'a> FnMut(mir::BodyLocation, &'a A::Domain),
    );
    fn semantics<A: MonotoneFramework>(
        db: &dyn crate::Db,
        a: &A,
        body: &mir::Body,
        facts: &mut HashMap<mir::BodyLocation, A::Domain>,
        bid: mir::BlockId,
    ) -> Progress;
    fn next(db: &dyn crate::Db, ib: &mir::ItemBody, bid: mir::BlockId, f: impl FnMut(mir::BlockId));
}

pub struct Forward;
pub struct Backward;

impl Direction for Forward {
    fn initial_blocks(_db: &dyn crate::Db, ib: &mir::ItemBody, mut f: impl FnMut(mir::BlockId)) {
        for bid in ib.entry_blocks() {
            f(bid);
        }
    }

    fn semantic<A: MonotoneFramework>(
        db: &dyn crate::Db,
        a: &A,
        body: &mir::Body,
        prev: &mut A::Domain,
        bid: mir::BlockId,
        mut events: impl for<'a> FnMut(mir::BodyLocation, &'a A::Domain),
    ) {
        for act in bid.actions(body) {
            let location = act.loc();
            a.semantic(db, body, act, prev);
            events(mir::BodyLocation::new(bid, location), prev)
        }
    }

    fn semantics<A: MonotoneFramework>(
        db: &dyn crate::Db,
        a: &A,
        body: &mir::Body,
        facts: &mut HashMap<mir::BodyLocation, A::Domain>,
        bid: mir::BlockId,
    ) -> Progress {
        let mut progress = Progress::No;

        for d in body.preceding_blocks(db, bid) {
            let mut prev = facts
                .entry(mir::BodyLocation::terminator_of(d))
                .or_insert_with(|| A::Domain::bottom(body))
                .clone();
            Self::semantic(db, a, body, &mut prev, bid, |loc, d| {
                let prev = facts.entry(loc).or_insert_with(|| A::Domain::bottom(body));
                if !prev.contains(body, d) {
                    progress = Progress::Yes;
                    prev.lub_extend(body, d);
                }
            });
        }

        progress
    }

    fn next(
        db: &dyn crate::Db,
        ib: &mir::ItemBody,
        bid: mir::BlockId,
        mut f: impl FnMut(mir::BlockId),
    ) {
        for b in ib.succeeding_blocks(db, bid) {
            f(b);
        }
    }
}
impl Direction for Backward {
    fn initial_blocks(db: &dyn crate::Db, ib: &mir::ItemBody, mut f: impl FnMut(mir::BlockId)) {
        for bid in ib.exit_blocks(db) {
            f(bid);
        }
    }

    fn semantic<A: MonotoneFramework>(
        db: &dyn crate::Db,
        a: &A,
        body: &mir::Body,
        prev: &mut A::Domain,
        bid: mir::BlockId,
        mut events: impl for<'a> FnMut(mir::BodyLocation, &'a A::Domain),
    ) {
        for op in bid.actions_rev(body) {
            let location = op.loc();
            a.semantic(db, body, op, prev);
            events(mir::BodyLocation::new(bid, location), prev)
        }
    }

    fn semantics<A: MonotoneFramework>(
        db: &dyn crate::Db,
        a: &A,
        body: &mir::Body,
        facts: &mut HashMap<mir::BodyLocation, A::Domain>,
        bid: mir::BlockId,
    ) -> Progress {
        let mut progress = Progress::No;

        for d in body.succeeding_blocks(db, bid) {
            let initial_loc = d.first_loc(body);
            let mut prev = facts
                .entry(mir::BodyLocation::new(d, initial_loc))
                .or_insert_with(|| A::Domain::bottom(body))
                .clone();
            Self::semantic(db, a, body, &mut prev, bid, |loc, d| {
                let prev = facts.entry(loc).or_insert_with(|| A::Domain::bottom(body));
                if !prev.contains(body, d) {
                    progress = Progress::Yes;
                    prev.lub_extend(body, d);
                }
            });
        }

        progress
    }

    fn next(
        db: &dyn crate::Db,
        ib: &mir::ItemBody,
        bid: mir::BlockId,
        mut f: impl FnMut(mir::BlockId),
    ) {
        for b in ib.preceding_blocks(db, bid) {
            f(b);
        }
    }
}

pub trait MonotoneFramework {
    type Domain: Lattice<mir::Body> + fmt::Debug;
    type Direction: Direction;
    fn semantic(
        &self,
        db: &dyn crate::Db,
        body: &mir::Body,
        act: mir::Action,
        prev: &mut Self::Domain,
    );
    fn initial(&self, db: &dyn crate::Db, ib: &mir::ItemBody) -> Self::Domain;
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
    db: &dyn crate::Db,
    a: A,
    ib: &mir::ItemBody,
) -> AnalysisResults<A> {
    let mut worklist = W::empty();

    let mut facts: HashMap<mir::BodyLocation, A::Domain> = Default::default();
    for bid in ib.blocks() {
        worklist.insert(bid);
    }

    let initial = a.initial(db, ib);
    A::Direction::initial_blocks(db, ib, |bid| {
        let mut called = false;
        let mut prev = initial.clone();
        A::Direction::semantic(db, &a, ib, &mut prev, bid, |loc, d| {
            called = true;
            facts.insert(loc, d.clone());
        });
        if !called {
            facts.insert(bid.first_body_loc(ib), prev);
        }
    });

    let mut calls = 0;

    while let Some(n) = worklist.extract() {
        calls += 1;

        match A::Direction::semantics(db, &a, ib, &mut facts, n) {
            Progress::No => {}
            Progress::Yes => A::Direction::next(db, ib, n, |b| worklist.insert(b)),
        }
    }

    AnalysisResults { facts, semantic_calls: calls }
}

impl<A> AnalysisResults<A>
where
    A: MonotoneFramework,
{
    pub fn entry(&self, loc: mir::BodyLocation) -> &A::Domain
    where
        A: MonotoneFramework<Direction = Backward>,
    {
        self.value_at(loc)
    }
    pub fn exit(&self, loc: mir::BodyLocation) -> &A::Domain
    where
        A: MonotoneFramework<Direction = Forward>,
    {
        self.value_at(loc)
    }
    pub fn try_entry(&self, loc: mir::BodyLocation) -> Option<&A::Domain>
    where
        A: MonotoneFramework<Direction = Backward>,
    {
        self.try_value_at(loc)
    }
    pub fn try_exit(&self, loc: mir::BodyLocation) -> Option<&A::Domain>
    where
        A: MonotoneFramework<Direction = Forward>,
    {
        self.try_value_at(loc)
    }
    /// Returns the value computed as the given block. Depending on the
    /// direction of the analysis, the value will be placed differently on the
    /// graph:
    /// - [`Forward`]: value at **exit** of the node is returned,
    /// - [`Backward`]: value to **entry** of the node is returned.
    pub fn value_at(&self, loc: mir::BodyLocation) -> &A::Domain {
        &self.facts[&loc]
    }
    /// Returns the value computed as the given block. Depending on the
    /// direction of the analysis, the value will be placed differently on the
    /// graph:
    /// - [`Forward`]: value at **exit** of the node is returned,
    /// - [`Backward`]: value to **entry** of the node is returned.
    pub fn try_value_at(&self, loc: mir::BodyLocation) -> Option<&A::Domain> {
        self.facts.get(&loc)
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
        other.iter().all(
            |(k, a)| {
                if let Some(b) = self.get(k) {
                    b.contains(ctx, a)
                } else {
                    false
                }
            },
        )
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
        other.iter().all(
            |(k, a)| {
                if let Some(b) = self.get(k) {
                    b.contains(ctx, a)
                } else {
                    false
                }
            },
        )
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
