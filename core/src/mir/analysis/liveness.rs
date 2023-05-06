use crate::{mir, util::IdxSet};

use super::monotone::{self, mono_analysis, MonotoneFramework};

pub type Liveness = monotone::AnalysisResults<LivenessAnalysis>;

impl Liveness {
    pub fn compute(body: &mir::Body) -> Self {
        mono_analysis::<_, monotone::FiFo>(LivenessAnalysis, body)
    }
}

pub struct LivenessAnalysis;

impl MonotoneFramework for LivenessAnalysis {
    type Domain = IdxSet<mir::SlotId>;

    type Direction = monotone::Backward;

    fn instruction_semantic(
        &self,
        body: &mir::Body,
        inst: mir::InstructionId,
        prev: &mut Self::Domain,
    ) {
        for p in body[inst].places_written_to() {
            prev.remove(p.slot);
        }
        for p in body[inst].places_referenced() {
            prev.insert(p.slot);
        }
    }

    fn terminator_semantic(
        &self,
        _body: &mir::Body,
        terminator: &mir::Terminator,
        prev: &mut Self::Domain,
    ) {
        for p in terminator.places_written_to() {
            prev.remove(p.slot);
        }
        for p in terminator.places_referenced() {
            prev.insert(p.slot);
        }
    }

    fn initial(&self, _body: &mir::Body) -> Self::Domain {
        Default::default()
    }
}
