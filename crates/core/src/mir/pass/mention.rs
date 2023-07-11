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
            let mut entry = scc.entry();
            while let Some(term) = entry.terminator(ib) {
                if term.targets(db).len() > 1 {
                    break;
                }
                entry = term.targets(db)[0];
            }
            let entry_loc = entry.first_body_loc(ib);
            let mut seen = IdxSet::default();
            for s in ib.locals_referenced(db, scc.blocks()) {
                if liveness.entry(entry_loc).contains_idx(s) {
                    seen.insert(s);
                }
            }
            for s in seen.iter() {
                let s_ty = &s.ty(db, ib);
                if !s_ty.is_ref(db) && !s_ty.is_adt(db) {
                    continue;
                }

                if let Some(t) = entry.terminator(ib) {
                    for bid in t.targets(db) {
                        // TODO: This should really be `first_body_loc`
                        let loc = bid.last_body_loc();
                        let place = ib.place(db, s);
                        ib.insert_instruction_before(loc, Instruction::PlaceMention(place));
                    }
                }

                let loc = entry.last_body_loc();
                let place = ib.place(db, s);
                ib.insert_instruction_before(loc, Instruction::PlaceMention(place));
            }
        }
    }
}
