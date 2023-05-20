use crate::{hir, mir, util::IdxSet};

use super::{
    folding_tree::FoldingTree,
    monotone::{self, mono_analysis, MonotoneFramework},
};

pub type Liveness = monotone::AnalysisResults<LivenessAnalysis>;

impl Liveness {
    pub fn compute(cx: &hir::ItemContext, body: &mir::Body) -> Self {
        mono_analysis::<_, monotone::FiFo>(LivenessAnalysis, cx, body)
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

    fn initial(&self, _cx: &hir::ItemContext, _body: &mir::Body) -> Self::Domain {
        Default::default()
    }
}

pub type FoldingAnalysisResults = monotone::AnalysisResults<FoldingAnalysis>;

impl FoldingAnalysisResults {
    pub fn compute(cx: &hir::ItemContext, body: &mir::Body) -> Self {
        mono_analysis::<_, monotone::FiFo>(FoldingAnalysis, cx, body)
    }
}

pub struct FoldingAnalysis;

impl MonotoneFramework for FoldingAnalysis {
    type Domain = FoldingTree;

    type Direction = monotone::Backward;

    fn instruction_semantic(
        &self,
        body: &mir::Body,
        inst: mir::InstructionId,
        prev: &mut Self::Domain,
    ) {
        prev.backwards_instruction_transition(body, inst)
    }

    fn terminator_semantic(
        &self,
        body: &mir::Body,
        terminator: &mir::Terminator,
        prev: &mut Self::Domain,
    ) {
        prev.backwards_terminator_transition(body, terminator)
    }

    fn initial(&self, cx: &hir::ItemContext, body: &mir::Body) -> Self::Domain {
        // TODO: We should look at params, return type, and post-conditions, to
        // see which slots should be folded at the exit
        let mut t = FoldingTree::default();
        for &param in body.params() {
            if let hir::TypeData::Ref { .. } = cx.ty_data_without_ghost(body.slot_ty(param)) {
                t.require(body, None, param.into());
            }
        }
        t
    }
}