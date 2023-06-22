use derive_new::new;
use folding_tree::RequireType;

use crate::mir::{
    analysis::{cfg::Cfg, folding_forrest::FoldingForrest, liveness, monotone::MonotoneFramework},
    BodyLocation, Folding, Instruction, ItemBody,
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
    fn run(db: &dyn crate::Db, ib: &mut ItemBody) {
        let folding_analysis = liveness::FoldingAnalysisResults::compute(db, ib);
        let mut internal_foldings: Vec<InternalFolding> = Vec::new();

        let cfg = Cfg::compute(db, ib);

        let mut tree_from_params = FoldingForrest::default();
        let mut tree_from_returns = FoldingForrest::default();
        for &s in ib.params() {
            tree_from_params.require(db, None, RequireType::Folded, ib.place(db, s));
            if s.ty(db, ib).is_ref(db) {
                tree_from_returns.require(db, None, RequireType::Folded, ib.place(db, s));
            }
        }
        if let Some(s) = ib.result_slot() {
            tree_from_returns.require(db, None, RequireType::Folded, ib.place(db, s));
        }
        let tree_from_params = tree_from_params;
        let tree_from_returns = tree_from_returns;

        let mut external_foldings = vec![];

        for entry in ib.entry_blocks() {
            cfg.visit_reverse_post_order(entry, |bid| {
                let mut current = folding_analysis.entry(bid.first_body_loc(ib)).clone();

                for act in bid.actions(ib) {
                    let loc = act.loc().in_block(bid);
                    for folding in
                        current.compute_transition_into(db, ib, folding_analysis.entry(loc))
                    {
                        internal_foldings.push(InternalFolding::new(loc, folding));
                    }
                    current.forwards_transition(db, ib, act);
                }
                let outgoing = current;
                let termination_folding = liveness::FoldingAnalysis.initial(db, ib);

                if ib.succeeding_blocks(db, bid).next().is_none() {
                    let mut outgoing = outgoing;
                    let foldings = outgoing.compute_transition_into(db, ib, &termination_folding);
                    if !foldings.is_empty() {
                        external_foldings.push((bid, None, foldings));
                    }
                } else {
                    for next in ib.succeeding_blocks(db, bid) {
                        let foldings = outgoing.clone().compute_transition_into(
                            db,
                            ib,
                            folding_analysis.entry(next.first_body_loc(ib)),
                        );
                        if !foldings.is_empty() {
                            external_foldings.push((bid, Some(next), foldings));
                        }
                    }
                }
            });
        }

        for bid in ib.entry_blocks() {
            let first_loc = bid.first_body_loc(ib);
            let mut tree = if ib.is_ensures(bid) {
                tree_from_returns.clone()
            } else {
                tree_from_params.clone()
            };
            for folding in tree.compute_transition_into(db, ib, folding_analysis.entry(first_loc)) {
                internal_foldings.push(InternalFolding::new(first_loc, folding))
            }
        }

        for t in internal_foldings {
            ib.insert_instruction_before(t.loc, Instruction::Folding(t.folding));
        }

        for (from, into, foldings) in external_foldings {
            match into {
                None => {
                    for f in foldings {
                        ib.insert_instruction_before(
                            BodyLocation::terminator_of(from),
                            Instruction::Folding(f),
                        );
                    }
                }
                Some(into) => {
                    ib.intersperse_instructions(
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
