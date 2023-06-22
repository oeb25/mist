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
    fn run(db: &dyn crate::Db, body: &mut crate::mir::Body) {
        let liveness = liveness::Liveness::compute(db, body);

        let cfg = Cfg::compute(db, body);

        for scc in cfg.scc() {
            let entry_loc = body.first_loc_in(scc.entry());
            let mut seen = IdxSet::default();
            for s in body.slots_referenced(db, scc.blocks()) {
                if liveness.entry(entry_loc).contains_idx(s) {
                    seen.insert(s);
                }
            }
            for s in seen.iter() {
                body.insert_instruction_before(
                    body.first_loc_in(scc.entry()),
                    Instruction::PlaceMention(s.into()),
                );
            }
        }
    }
}
