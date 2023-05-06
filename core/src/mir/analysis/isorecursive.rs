use std::collections::HashMap;

use derive_new::new;
use tracing::warn;

use crate::{
    hir::ItemContext,
    mir::{BlockId, BlockLocation, Body, BodyLocation, Folding, Instruction, Place},
    util::{IdxMap, IdxSet},
};

use super::{cfg::Cfg, liveness};

#[derive(new, Debug, PartialEq, Eq)]
pub struct IsorecursivePass<'a> {
    cx: &'a ItemContext,
    body: &'a mut Body,
    #[new(default)]
    constraints: IdxMap<BlockId, Constraint>,
}

#[derive(new, Debug, Default, Clone, PartialEq, Eq)]
struct Constraint {
    entry: FoldingTree,
    exit: FoldingTree,
}

/// A folding happening within a block
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
struct InternalFolding {
    loc: BodyLocation,
    folding: Folding,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FoldingNode {
    Folded,
    Unfolded { children: Vec<Place> },
}

/// A [`FoldingTree`] maintains the the state of foldings and unfoldings of
/// [slots](crate::mir::Slot) and their projections.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
struct FoldingTree {
    nodes: HashMap<Place, (Option<BlockLocation>, FoldingNode)>,
}

impl FoldingTree {
    fn node(&self, place: Place) -> (Option<BlockLocation>, FoldingNode) {
        self.nodes
            .get(&place)
            .cloned()
            .unwrap_or((None, FoldingNode::Folded))
    }
    fn remove_node(&mut self, place: Place) -> (Option<BlockLocation>, FoldingNode) {
        self.nodes
            .remove(&place)
            .unwrap_or((None, FoldingNode::Folded))
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
                        if loc == prev_loc {
                            warn!("unfolding something that was folded at same loc");
                        }

                        foldings.push(Folding::Unfold {
                            consume: place,
                            into: vec![],
                        });
                        self.nodes
                            .insert(place, (loc, FoldingNode::Unfolded { children: vec![] }));
                        let Some(parent_place) = place.parent(body) else { continue };
                        if let Some((_, FoldingNode::Unfolded { children })) =
                            self.nodes.get_mut(&parent_place)
                        {
                            if !children.contains(&place) {
                                children.push(place)
                            }
                        }
                    }
                    (_, FoldingNode::Unfolded { .. }) => {}
                }
            }
        }

        let folding_start = foldings.len();
        let mut folding_queue = vec![place.replace_projection(last.unwrap())];
        while let Some(place) = folding_queue.pop() {
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
                        folding_queue.push(child);
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

        for k in target.nodes.keys() {
            for folding in self.require(body, None, *k) {
                foldings.push(folding);
            }
        }

        foldings
    }
}

impl IsorecursivePass<'_> {
    /// Run the pass from the given block
    // #[tracing::instrument(name = "IsorecursivePass", skip(self))]
    pub fn run(&mut self, entry: BlockId) {
        let result = liveness::Liveness::compute(self.body);

        let cfg = Cfg::compute(self.body);

        for scc in cfg.scc() {
            let mut seen = IdxSet::default();
            for s in self.body.slots_referenced(scc.blocks()) {
                if result.entry(scc.entry()).contains_idx(s) {
                    seen.insert(s);
                }
            }
            dbg!(&seen);
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
            dbg!(&folding_tree);
            if let Some(old) = self.constraints.insert(
                scc.entry(),
                Constraint {
                    entry: folding_tree.clone(),
                    exit: folding_tree,
                },
            ) {
                todo!("entry node was part of multiple scc: {old:?}")
            }
        }

        let cfg = Cfg::compute(self.body);

        let mut post_resolutions = vec![];
        let mut post_merges = vec![];

        cfg.visit_reverse_post_order(entry, |bid| {
            let incomming = cfg
                .direct_predecessors(bid)
                .filter_map(|b| {
                    if let Some(c) = self.constraints.get(b) {
                        Some((b, c.exit.clone()))
                    } else {
                        post_resolutions.push((b, bid));
                        None
                    }
                })
                .reduce(|(_, acc), (b, c)| {
                    if acc == c {
                        (b, acc)
                    } else {
                        post_merges.push((b, bid));
                        (b, acc)
                    }
                })
                .map(|(_, c)| c)
                .unwrap_or_default();

            let (c, internal_foldings) = self.compute_block_exit_folding(incomming.clone(), bid);
            if self.constraints.contains_idx(bid) {
                warn!("constraint was already computed");
            } else {
                self.constraints.insert(bid, Constraint::new(incomming, c));
            }

            for t in internal_foldings {
                self.body
                    .insert_instruction_before(t.loc, Instruction::Folding(t.folding));
            }
        });

        for (from, into) in post_resolutions.into_iter().chain(post_merges) {
            let transition_entry = self.constraints[from].exit.clone();
            let mut transition_exit = transition_entry.clone();
            let internal_foldings =
                transition_exit.compute_transition_into(self.body, &self.constraints[into].entry);

            warn!(
                    "need to resolve transition from {:?} into {:?} with foldings {internal_foldings:?} ({} -> {})",
                    self.constraints[from],
                    self.constraints[into],
                    from,
                    into,
                );

            self.body.intersperse_instructions(
                from,
                into,
                internal_foldings.into_iter().map(Instruction::Folding),
            );
        }
    }

    #[must_use]
    fn compute_block_exit_folding(
        &self,
        incomming: FoldingTree,
        bid: BlockId,
    ) -> (FoldingTree, Vec<InternalFolding>) {
        let mut c = incomming;

        let mut internal_foldings = vec![];

        for &inst in self.body[bid].instructions() {
            let loc = BodyLocation::new(bid, inst.into());
            for place in self.body[inst].places_referenced() {
                for folding in c.require(self.body, Some(inst.into()), place) {
                    internal_foldings.push(InternalFolding::new(loc, folding));
                }
            }
            for place in self.body[inst].places_written_to() {
                c.drop(place);
            }
        }

        if let Some(term) = self.body[bid].terminator() {
            let loc = BodyLocation::new(bid, BlockLocation::Terminator);
            for place in term.places_referenced() {
                for folding in c.require(self.body, Some(BlockLocation::Terminator), place) {
                    internal_foldings.push(InternalFolding::new(loc, folding));
                }
            }
            for place in term.places_written_to() {
                c.drop(place);
            }
        }

        (c, internal_foldings)
    }
}
