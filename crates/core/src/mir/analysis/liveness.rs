use folding_tree::RequireType;

use crate::{mir, mono::types::TypeData, util::IdxSet};

use super::{
    folding_tree::FoldingTree,
    monotone::{self, mono_analysis, MonotoneFramework},
};

pub type Liveness = monotone::AnalysisResults<LivenessAnalysis>;

impl Liveness {
    pub fn compute(db: &dyn crate::Db, body: &mir::Body) -> Self {
        mono_analysis::<_, monotone::FiFo>(db, LivenessAnalysis, body)
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
        for p in body[inst].places_referenced(body) {
            prev.insert(p.slot);
        }
    }

    fn terminator_semantic(
        &self,
        body: &mir::Body,
        terminator: &mir::Terminator,
        prev: &mut Self::Domain,
    ) {
        for p in terminator.places_written_to() {
            prev.remove(p.slot);
        }
        for p in terminator.places_referenced(body) {
            prev.insert(p.slot);
        }
    }

    fn initial(&self, _db: &dyn crate::Db, _body: &mir::Body) -> Self::Domain {
        Default::default()
    }
}

pub type FoldingAnalysisResults = monotone::AnalysisResults<FoldingAnalysis>;

impl FoldingAnalysisResults {
    pub fn compute(db: &dyn crate::Db, body: &mir::Body) -> Self {
        mono_analysis::<_, monotone::FiFo>(db, FoldingAnalysis, body)
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

    fn initial(&self, db: &dyn crate::Db, body: &mir::Body) -> Self::Domain {
        // TODO: We should look at params, return type, and post-conditions, to
        // see which slots should be folded at the exit
        let mut t = FoldingTree::default();
        for &param in body.params() {
            if let TypeData::Ref { .. } = body.slot_ty(db, param).kind(db) {
                t.require(body, None, RequireType::Folded, param.into());
            }
        }
        t
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use salsa::ParallelDatabase;
    use tracing::{info, Level};

    use crate::{db::Database, hir, mir, mono};

    fn generate_annotated_mir(src: &str) -> String {
        let db = Database::default();
        let file = hir::SourceFile::new(&db, src.to_string());
        mono::monomorphized_items(&db, file)
            .items(&db)
            .iter()
            .filter_map(|&item| {
                info!("{}", item.name(&db));
                let span = tracing::span!(Level::DEBUG, "dump", item = item.name(&db).to_string());
                let _enter = span.enter();

                let mir = mir::lower_item(&db, item)?.body(&db);

                let a = mir::analysis::liveness::FoldingAnalysisResults::compute(&db, mir);
                let db2 = db.snapshot();
                let mir2 = mir.clone();
                let serialized = mir.serialize_with_annotation(
                    &db,
                    mir::serialize::Color::No,
                    Box::new(move |loc| {
                        let mut x = a.try_entry(loc)?.clone();
                        let incomming = x.debug_str(&*db2, &mir2);
                        match loc.inner {
                            mir::BlockLocation::Instruction(inst) => {
                                x.forwards_instruction_transition(&mir2, inst)
                            }
                            mir::BlockLocation::Terminator => x.forwards_terminator_transition(
                                &mir2,
                                mir2[loc.block].terminator.as_ref()?,
                            ),
                        }
                        let outgoing = x.debug_str(&*db2, &mir2);
                        Some(format!("{incomming}\n> {outgoing}"))
                    }),
                );
                if serialized.is_empty() {
                    None
                } else {
                    Some(serialized)
                }
            })
            .join("\n\n")
            .trim()
            .to_string()
    }

    #[test]
    fn test_01() {
        let src = "fn main() { let x = 12; }";
        insta::assert_display_snapshot!(generate_annotated_mir(src), @r###"
        :B0
          {%0: @}
        > {%0: @}
          !goto :B1
        :B1
          {%0: @}
        > {%0: X}
          %0 := $12
        "###)
    }

    #[test]
    fn test_02() {
        let src = r#"
            struct T { n: int }
            fn main() -> T {
                let x = T { n: 12 };
                assert x.n == 12;
                x
            }
        "#;
        insta::assert_display_snapshot!(generate_annotated_mir(src), @r###"
        :B0
          {%result: @, %1: @}
        > {%result: @, %1: @}
          !goto :B1
        :B1
          {%result: @, %1: @}
        > {%result: @, %1: X}
          %1 := T { n: $12 }
          {%result: @, %1: { .n X }}
        > {%result: @, %1: { .n X }}
          assert (== %1.n $12)
          {%result: @, %1: X}
        > {%result: X, %1: X}
          %result := %1
        "###)
    }

    #[test]
    fn test_03() {
        let src = r#"
            struct T { n: int }
            fn init(p: T) {
                p.n = p.n + 1;
            }
        "#;
        insta::assert_display_snapshot!(generate_annotated_mir(src), @r###"
        :B0
          {%0: { .n X }, %1: @}
        > {%0: { .n X }, %1: @}
          !goto :B1
        :B1
          {%0: { .n X }, %1: @}
        > {%0: { .n X }, %1: X}
          %1 := (+ %0.n $1)
          {%0: { .n X }, %1: X}
        > {%0: { .n X }, %1: X}
          %0.n := %1
        "###)
    }

    #[test]
    fn test_04() {
        let src = r#"
            struct T { n: int, t: T }
            fn init(p: T) {
                p.t = p;
                p.n = p.n + 1;
                p.t.n = p.n;
            }
        "#;
        insta::assert_display_snapshot!(generate_annotated_mir(src), @r###"
        :B0
          {%0: X, %1: @}
        > {%0: X, %1: @}
          !goto :B1
        :B1
          {%0: X, %1: @}
        > {%0: { .t X .n X }, %1: @}
          %0.t := %0
          {%0: { .t { .n X } .n X }, %1: @}
        > {%0: { .t { .n X } .n X }, %1: X}
          %1 := (+ %0.n $1)
          {%0: { .t { .n X } .n @ }, %1: X}
        > {%0: { .t { .n X } .n X }, %1: X}
          %0.n := %1
          {%0: { .t { .n X } .n X }}
        > {%0: { .t { .n X } .n X }}
          %0.t.n := %0.n
        "###)
    }

    #[test]
    fn test_05() {
        let src = r#"
            struct T { n: int }
            fn f() {
                let ts: [T] = [T { n: 0 }];
                ts[0].n = 15;
            }
        "#;
        insta::assert_display_snapshot!(generate_annotated_mir(src), @r###"
        :B0
          {%0: @, %1: @, %2: @}
        > {%0: @, %1: @, %2: @}
          !goto :B1
        :B1
          {%0: @, %1: @, %2: @}
        > {%0: @, %1: X, %2: @}
          %1 := T { n: $0 }
          {%0: @, %1: X, %2: @}
        > {%0: X, %1: X, %2: @}
          !call %0 := (#list %1) -> :B2
        :B2
          {%0: { [%2] { .n X } }, %2: @}
        > {%0: { [%2] { .n X } }, %2: X}
          %2 := $0
          {%0: { [%2] { .n X } }}
        > {%0: { [%2] { .n X } }}
          %0[%2].n := $15
        "###)
    }
}
