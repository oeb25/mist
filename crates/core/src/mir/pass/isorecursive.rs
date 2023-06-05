use derive_new::new;

use crate::mir::{
    analysis::{cfg::Cfg, folding_tree::FoldingTree, liveness, monotone::MonotoneFramework},
    BlockLocation, Body, BodyLocation, Folding, Instruction,
};

use super::Pass;

pub struct IsorecursivePass {}

/// A folding happening within a block
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
struct InternalFolding {
    loc: BodyLocation,
    folding: Folding,
}

impl Pass for IsorecursivePass {
    #[tracing::instrument(name = "IsorecursivePass", skip_all)]
    fn run(_db: &dyn crate::Db, body: &mut Body) {
        let folding_analysis = liveness::FoldingAnalysisResults::compute(body);
        let mut internal_foldings: Vec<InternalFolding> = Vec::new();

        let cfg = Cfg::compute(body);

        let mut tree_from_params = FoldingTree::default();
        for &s in body.params() {
            tree_from_params.require(body, None, s.into());
        }
        let tree_from_params = tree_from_params;

        let mut external_foldings = vec![];

        for entry in body.entry_blocks() {
            cfg.visit_reverse_post_order(entry, |bid| {
                let mut current = folding_analysis.entry(body.first_loc_in(bid)).clone();

                for loc in body.locations_in(bid) {
                    for folding in current.compute_transition_into(folding_analysis.entry(loc)) {
                        internal_foldings.push(InternalFolding::new(loc, folding));
                    }
                    match loc.inner {
                        BlockLocation::Instruction(inst) => {
                            current.forwards_instruction_transition(body, inst)
                        }
                        BlockLocation::Terminator => current
                            .forwards_terminator_transition(body, body[bid].terminator().unwrap()),
                    }
                }
                let outgoing = current;
                let termination_folding = liveness::FoldingAnalysis.initial(body);

                if body.succeeding_blocks(bid).next().is_none() {
                    let mut outgoing = outgoing;
                    let foldings = outgoing.compute_transition_into(&termination_folding);
                    if !foldings.is_empty() {
                        external_foldings.push((bid, None, foldings));
                    }
                } else {
                    for next in body.succeeding_blocks(bid) {
                        let foldings = outgoing.clone().compute_transition_into(
                            folding_analysis.entry(body.first_loc_in(next)),
                        );
                        if !foldings.is_empty() {
                            external_foldings.push((bid, Some(next), foldings));
                        }
                    }
                }
            });
        }

        for bid in body.entry_blocks() {
            let first_inst_or_terminator = body[bid].first_loc();
            for folding in tree_from_params
                .clone()
                .compute_transition_into(folding_analysis.entry(body.first_loc_in(bid)))
            {
                internal_foldings.push(InternalFolding::new(
                    BodyLocation::new(bid, first_inst_or_terminator),
                    folding,
                ))
            }
        }

        for t in internal_foldings {
            body.insert_instruction_before(t.loc, Instruction::Folding(t.folding));
        }

        for (from, into, foldings) in external_foldings {
            match into {
                None => {
                    for f in foldings {
                        body.insert_instruction_before(
                            BodyLocation::new(from, BlockLocation::Terminator),
                            Instruction::Folding(f),
                        );
                    }
                }
                Some(into) => {
                    body.intersperse_instructions(
                        from,
                        into,
                        foldings.into_iter().map(Instruction::Folding),
                    );
                }
            }
        }
    }
}