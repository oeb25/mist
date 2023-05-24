use derive_new::new;

use crate::{
    mir::{BlockLocation, Body, BodyLocation, Folding, Instruction},
    util::IdxSet,
};

use super::{cfg::Cfg, folding_tree::FoldingTree, liveness, monotone::MonotoneFramework};

#[derive(new)]
pub struct IsorecursivePass<'a> {
    body: &'a mut Body,
}

/// A folding happening within a block
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
struct InternalFolding {
    loc: BodyLocation,
    folding: Folding,
}

impl IsorecursivePass<'_> {
    /// Run the pass from the given block
    // #[tracing::instrument(name = "IsorecursivePass", skip(self))]
    pub fn run(&mut self) {
        let liveness = liveness::Liveness::compute(self.body);

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

        let folding_analysis = liveness::FoldingAnalysisResults::compute(self.body);
        let mut internal_foldings: Vec<InternalFolding> = Vec::new();

        let cfg = Cfg::compute(self.body);

        let mut external_foldings = vec![];

        for entry in self.body.entry_blocks() {
            cfg.visit_reverse_post_order(entry, |bid| {
                let mut current = folding_analysis.entry(bid).clone();

                for &inst in self.body[bid].instructions.iter() {
                    let mut prev = current.clone();
                    current.forwards_instruction_transition(self.body, inst);
                    for folding in prev.compute_transition_into(&current) {
                        internal_foldings.push(InternalFolding::new(
                            BodyLocation::new(bid, BlockLocation::Instruction(inst)),
                            folding,
                        ));
                    }
                }
                if let Some(terminator) = &self.body[bid].terminator {
                    let mut prev = current.clone();
                    current.forwards_terminator_transition(self.body, terminator);
                    for folding in prev.compute_transition_into(&current) {
                        internal_foldings.push(InternalFolding::new(
                            BodyLocation::new(bid, BlockLocation::Terminator),
                            folding,
                        ));
                    }
                }
                let outgoing = current;
                let termination_folding = liveness::FoldingAnalysis.initial(self.body);

                if self.body.succeeding_blocks(bid).next().is_none() {
                    let mut outgoing = outgoing;
                    let foldings = outgoing.compute_transition_into(&termination_folding);
                    if !foldings.is_empty() {
                        external_foldings.push((bid, None, foldings));
                    }
                } else {
                    for next in self.body.succeeding_blocks(bid) {
                        let foldings = outgoing
                            .clone()
                            .compute_transition_into(folding_analysis.entry(next));
                        if !foldings.is_empty() {
                            external_foldings.push((bid, Some(next), foldings));
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
                .compute_transition_into(folding_analysis.entry(bid))
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

        for (from, into, foldings) in external_foldings {
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
