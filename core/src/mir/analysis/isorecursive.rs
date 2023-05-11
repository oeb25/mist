use std::collections::{HashMap, HashSet};

use derive_new::new;
use itertools::Itertools;
use tracing::warn;

use crate::{
    hir::ItemContext,
    mir::{self, BlockLocation, Body, BodyLocation, Folding, Instruction, Place},
    util::IdxSet,
};

use super::{cfg::Cfg, liveness, monotone::MonotoneFramework};

#[derive(new)]
pub struct IsorecursivePass<'a> {
    cx: &'a ItemContext,
    body: &'a mut Body,
}

/// A folding happening within a block
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
struct InternalFolding {
    loc: BodyLocation,
    folding: Folding,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum FoldingNode {
    Unfolded { children: HashSet<Place> },
    Folded,
}

impl Default for FoldingNode {
    fn default() -> Self {
        FoldingNode::Unfolded {
            children: HashSet::new(),
        }
    }
}

/// A [`FoldingTree`] maintains the the state of foldings and unfoldings of
/// [slots](crate::mir::Slot) and their projections.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct FoldingTree {
    nodes: HashMap<Place, (Option<BlockLocation>, FoldingNode)>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum InvariantError {
    ChildrenEmpty,
    ChildMissing,
    ParentDoesNotContainChild,
    ParentMissing,
    ParentFolded,
}

impl FoldingTree {
    fn node(&self, place: Place) -> (Option<BlockLocation>, FoldingNode) {
        self.nodes.get(&place).cloned().unwrap_or_default()
    }
    fn remove_node(&mut self, place: Place) -> (Option<BlockLocation>, FoldingNode) {
        self.nodes.remove(&place).unwrap_or_default()
    }
    pub fn invariant(&self, body: &Body) -> Result<(), InvariantError> {
        for (p, (_, folding)) in &self.nodes {
            match folding {
                FoldingNode::Unfolded { children } => {
                    if children.is_empty() {
                        return Err(InvariantError::ChildrenEmpty);
                    }
                    for child in children {
                        if !self.nodes.contains_key(child) {
                            return Err(InvariantError::ChildMissing);
                        }
                    }
                }
                FoldingNode::Folded => {
                    if let Some(parent) = p.parent(body) {
                        if let Some((_, parent_folding)) = self.nodes.get(&parent) {
                            match parent_folding {
                                FoldingNode::Unfolded { children } => {
                                    if !children.contains(p) {
                                        return Err(InvariantError::ParentDoesNotContainChild);
                                    }
                                }
                                FoldingNode::Folded => return Err(InvariantError::ParentFolded),
                            }
                        } else {
                            return Err(InvariantError::ParentMissing);
                        }
                    }
                }
            }
        }

        Ok(())
    }
    pub fn places(&self) -> impl Iterator<Item = Place> + '_ {
        self.nodes.keys().copied()
    }
    pub fn leafs(&self) -> impl Iterator<Item = Place> + '_ {
        self.nodes.iter().filter_map(|(k, (_, v))| match v {
            FoldingNode::Folded => Some(*k),
            FoldingNode::Unfolded { .. } => None,
        })
    }
    /// Computes the nessesary foldings and unfoldings for the given place to be
    /// accessible.
    pub fn require(
        &mut self,
        body: &Body,
        loc: Option<BlockLocation>,
        place: Place,
    ) -> Vec<Folding> {
        let mut foldings = vec![];

        let mut last = None;
        for p in body.projection_path_iter(place.projection) {
            if let Some(prev) = last.replace(p) {
                let place = place.replace_projection(prev);
                match self.node(place) {
                    (prev_loc, FoldingNode::Folded) => {
                        if loc.is_some() && loc == prev_loc {
                            warn!("unfolding something that was folded at same loc");
                        }

                        foldings.push(Folding::Unfold {
                            consume: place,
                            into: vec![],
                        });
                        self.nodes.insert(
                            place,
                            (
                                loc,
                                FoldingNode::Unfolded {
                                    children: Default::default(),
                                },
                            ),
                        );
                    }
                    (_, FoldingNode::Unfolded { .. }) => {}
                }
                if let Some(parent) = place.parent(body) {
                    match &mut self.nodes.entry(parent).or_default().1 {
                        FoldingNode::Unfolded { children } => {
                            children.insert(place);
                        }
                        FoldingNode::Folded => unreachable!(),
                    }
                }
            }
        }

        let last = place.replace_projection(last.unwrap());

        {
            let mut current = last;
            while let Some(next) = current.parent(body) {
                match &mut self.nodes.entry(next).or_default().1 {
                    FoldingNode::Unfolded { children } => {
                        children.insert(current);
                    }
                    FoldingNode::Folded => unreachable!(),
                }
                current = next;
            }
        }

        let folding_start = foldings.len();
        let mut folding_children_queue = match self.nodes.insert(last, (loc, FoldingNode::Folded)) {
            Some((_, FoldingNode::Unfolded { children })) => {
                foldings.push(Folding::Fold {
                    consume: vec![],
                    into: last,
                });
                children.into_iter().collect_vec()
            }
            None | Some((_, FoldingNode::Folded)) => Default::default(),
        };
        while let Some(place) = folding_children_queue.pop() {
            match self.remove_node(place) {
                (_, FoldingNode::Folded) => {}
                (prev_loc, FoldingNode::Unfolded { children }) => {
                    if loc == prev_loc {
                        warn!("folding something that was folded at same loc");
                    }

                    foldings.insert(
                        folding_start,
                        Folding::Fold {
                            consume: vec![],
                            into: place,
                        },
                    );
                    for child in children {
                        folding_children_queue.push(child);
                    }
                }
            }
        }

        if !place.has_projection(body) && !self.nodes.contains_key(&place) {
            self.nodes.insert(place, (None, FoldingNode::Folded));
        }

        foldings
    }
    /// Erases all fold state for the given place and transitively for all
    /// children.
    ///
    /// This is useful when performing an assignment to a place, where all
    /// previous unfoldings into that place are lost.
    pub fn drop(&mut self, place: Place) {
        let mut drop_queue = vec![place];
        while let Some(place) = drop_queue.pop() {
            match self.nodes.remove(&place) {
                None | Some((_, FoldingNode::Folded)) => {}
                Some((_, FoldingNode::Unfolded { children })) => {
                    for child in children {
                        drop_queue.push(child);
                    }
                }
            }
        }
    }

    fn compute_transition_into(&mut self, body: &Body, target: &FoldingTree) -> Vec<Folding> {
        let mut foldings = vec![];

        for k in target.leafs() {
            for folding in self.require(body, None, k) {
                foldings.push(folding);
            }
        }

        foldings
    }

    pub fn forwards_instruction_transition(&mut self, body: &mir::Body, inst: mir::InstructionId) {
        for p in body[inst].places_referenced() {
            let _ = self.require(body, None, p);
        }
        for p in body[inst].places_written_to() {
            self.drop(p);
            let _ = self.require(body, None, p);
        }
    }
    pub fn forwards_terminator_transition(
        &mut self,
        body: &mir::Body,
        terminator: &mir::Terminator,
    ) {
        for p in terminator.places_referenced() {
            let _ = self.require(body, None, p);
        }
        for p in terminator.places_written_to() {
            self.drop(p);
            let _ = self.require(body, None, p);
        }
    }
    pub fn backwards_instruction_transition(&mut self, body: &mir::Body, inst: mir::InstructionId) {
        for p in body[inst].places_written_to() {
            self.drop(p);
            let _ = self.require(body, None, p);
        }
        for p in body[inst].places_referenced() {
            let _ = self.require(body, None, p);
        }
    }
    pub fn backwards_terminator_transition(
        &mut self,
        body: &mir::Body,
        terminator: &mir::Terminator,
    ) {
        for p in terminator.places_written_to() {
            self.drop(p);
            let _ = self.require(body, None, p);
        }
        for p in terminator.places_referenced() {
            let _ = self.require(body, None, p);
        }
    }
}

impl IsorecursivePass<'_> {
    /// Run the pass from the given block
    // #[tracing::instrument(name = "IsorecursivePass", skip(self))]
    pub fn run(&mut self) {
        let liveness = liveness::Liveness::compute(self.cx, self.body);

        let cfg = Cfg::compute(self.body);

        for scc in cfg.scc() {
            let mut seen = IdxSet::default();
            for s in self.body.slots_referenced(scc.blocks()) {
                if liveness.entry(scc.entry()).contains_idx(s) {
                    seen.insert(s);
                }
            }
            let mut folding_tree = FoldingTree::default();
            for s in seen.iter() {
                let p = s.into();
                folding_tree.require(self.body, None, p);
                self.body.insert_instruction_before(
                    BodyLocation {
                        block: scc.entry(),
                        inner: BlockLocation::Terminator,
                    },
                    Instruction::PlaceMention(p),
                );
            }
        }

        let folding_liveness = liveness::FoldingLiveness::compute(self.cx, self.body);
        let mut internal_foldings: Vec<InternalFolding> = Vec::new();

        let cfg = Cfg::compute(self.body);

        let mut post_resolutions = vec![];

        for entry in self.body.entry_blocks() {
            cfg.visit_reverse_post_order(entry, |bid| {
                let mut current = folding_liveness.entry(bid).clone();

                for &inst in self.body[bid].instructions.iter() {
                    let mut prev = current.clone();
                    current.forwards_instruction_transition(self.body, inst);
                    for folding in prev.compute_transition_into(self.body, &current) {
                        internal_foldings.push(InternalFolding::new(
                            BodyLocation::new(bid, BlockLocation::Instruction(inst)),
                            folding,
                        ));
                    }
                }
                if let Some(terminator) = &self.body[bid].terminator {
                    let mut prev = current.clone();
                    current.forwards_terminator_transition(self.body, terminator);
                    for folding in prev.compute_transition_into(self.body, &current) {
                        internal_foldings.push(InternalFolding::new(
                            BodyLocation::new(bid, BlockLocation::Terminator),
                            folding,
                        ));
                    }
                }
                let outgoing = current;
                let termination_folding =
                    liveness::FoldingLivenessAnalysis.initial(self.cx, self.body);

                if self.body.succeeding_blocks(bid).next().is_none() {
                    let mut outgoing = outgoing;
                    let foldings =
                        outgoing.compute_transition_into(self.body, &termination_folding);
                    if !foldings.is_empty() {
                        post_resolutions.push((bid, None, foldings));
                    }
                } else {
                    for next in self.body.succeeding_blocks(bid) {
                        let foldings = outgoing
                            .clone()
                            .compute_transition_into(self.body, folding_liveness.entry(next));
                        if !foldings.is_empty() {
                            post_resolutions.push((bid, Some(next), foldings));
                        }
                    }
                }
            });
        }

        let mut tree_from_params = FoldingTree::default();
        for &s in self.body.params() {
            tree_from_params.require(self.body, None, s.into());
        }
        let tree_from_params = tree_from_params;

        for bid in self.body.entry_blocks() {
            let first_inst_or_terminator = self.body[bid]
                .instructions()
                .first()
                .map(|inst| BlockLocation::Instruction(*inst))
                .unwrap_or(BlockLocation::Terminator);
            for folding in tree_from_params
                .clone()
                .compute_transition_into(self.body, folding_liveness.entry(bid))
            {
                internal_foldings.push(InternalFolding::new(
                    BodyLocation::new(bid, first_inst_or_terminator),
                    folding,
                ))
            }
        }

        for t in internal_foldings {
            self.body
                .insert_instruction_before(t.loc, Instruction::Folding(t.folding));
        }

        for (from, into, foldings) in post_resolutions {
            match into {
                None => {
                    for f in foldings {
                        self.body.insert_instruction_before(
                            BodyLocation::new(from, BlockLocation::Terminator),
                            Instruction::Folding(f),
                        );
                    }
                }
                Some(into) => {
                    self.body.intersperse_instructions(
                        from,
                        into,
                        foldings.into_iter().map(Instruction::Folding),
                    );
                }
            }
        }
    }
}
