use crate::{
    mir::{
        analysis::{cfg::Cfg, liveness},
        Instruction,
    },
    util::IdxSet,
};

use super::Pass;

pub struct MentionPass;

impl Pass for MentionPass {
    fn run(db: &dyn crate::Db, ib: &mut crate::mir::ItemBody) {
        let liveness = liveness::Liveness::compute(db, ib);

        let cfg = Cfg::compute(db, ib);

        for scc in cfg.scc() {
            let entry_loc = scc.entry().first_body_loc(ib);
            let mut seen = IdxSet::default();
            for s in ib.slots_referenced(db, scc.blocks()) {
                if liveness.entry(entry_loc).contains_idx(s) {
                    seen.insert(s);
                }
            }
            for s in seen.iter() {
                let loc = scc.entry().first_body_loc(ib);
                let place = ib.place(db, s);
                ib.insert_instruction_before(loc, Instruction::PlaceMention(place));
            }
        }
    }
}
