use derive_new::new;
use folding_tree::RequireType;

use crate::{
    mir::{
        analysis::{cfg::Cfg, folding_tree::FoldingTree, liveness, monotone::MonotoneFramework},
        Body, BodyLocation, Folding, Instruction,
    },
    mono::types::TypeData,
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
    fn run(db: &dyn crate::Db, body: &mut Body) {
        let folding_analysis = liveness::FoldingAnalysisResults::compute(db, body);
        let mut internal_foldings: Vec<InternalFolding> = Vec::new();

        let cfg = Cfg::compute(db, body);

        let mut tree_from_params = FoldingTree::default();
        let mut tree_from_returns = FoldingTree::default();
        for &s in body.params() {
            tree_from_params.require(db, None, RequireType::Folded, s.into());
            if let TypeData::Ref { .. } = body.slot_ty(db, s).kind(db) {
                tree_from_returns.require(db, None, RequireType::Folded, s.into());
            }
        }
        if let Some(s) = body.result_slot() {
            tree_from_returns.require(db, None, RequireType::Folded, s.into());
        }
        let tree_from_params = tree_from_params;
        let tree_from_returns = tree_from_returns;

        let mut external_foldings = vec![];

        for entry in body.entry_blocks() {
            cfg.visit_reverse_post_order(entry, |bid| {
                let mut current = folding_analysis.entry(body.first_loc_in(bid)).clone();

                for act in body[bid].actions() {
                    let loc = act.loc().in_block(bid);
                    for folding in current.compute_transition_into(db, folding_analysis.entry(loc))
                    {
                        internal_foldings.push(InternalFolding::new(loc, folding));
                    }
                    current.forwards_transition(db, body, act);
                }
                let outgoing = current;
                let termination_folding = liveness::FoldingAnalysis.initial(db, body);

                if body.succeeding_blocks(db, bid).next().is_none() {
                    let mut outgoing = outgoing;
                    let foldings = outgoing.compute_transition_into(db, &termination_folding);
                    if !foldings.is_empty() {
                        external_foldings.push((bid, None, foldings));
                    }
                } else {
                    for next in body.succeeding_blocks(db, bid) {
                        let foldings = outgoing.clone().compute_transition_into(
                            db,
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
            let first_loc = body.first_loc_in(bid);
            let mut tree = if body.is_ensures(bid) {
                tree_from_returns.clone()
            } else {
                tree_from_params.clone()
            };
            for folding in tree.compute_transition_into(db, folding_analysis.entry(first_loc)) {
                internal_foldings.push(InternalFolding::new(first_loc, folding))
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
                            BodyLocation::terminator_of(from),
                            Instruction::Folding(f),
                        );
                    }
                }
                Some(into) => {
                    body.intersperse_instructions(
                        db,
                        from,
                        into,
                        foldings.into_iter().map(Instruction::Folding),
                    );
                }
            }
        }
    }
}
