use folding_tree::RequireType;

use crate::{mir, util::IdxSet};

use super::{
    folding_forrest::FoldingForrest,
    monotone::{self, mono_analysis, MonotoneFramework},
};

pub type Liveness = monotone::AnalysisResults<LivenessAnalysis>;

impl Liveness {
    pub fn compute(db: &dyn crate::Db, ib: &mir::ItemBody) -> Self {
        mono_analysis::<_, monotone::FiFo>(db, LivenessAnalysis, ib)
    }
}

pub struct LivenessAnalysis;

impl MonotoneFramework for LivenessAnalysis {
    type Domain = IdxSet<mir::LocalId>;

    type Direction = monotone::Backward;

    fn semantic(
        &self,
        db: &dyn crate::Db,
        body: &mir::Body,
        act: mir::Action,
        prev: &mut Self::Domain,
    ) {
        for p in act.places_written_to(db, body) {
            prev.remove(p.local());
        }
        for p in act.places_referenced(db, body) {
            prev.insert(p.local());
        }
    }

    fn initial(&self, _db: &dyn crate::Db, _ib: &mir::ItemBody) -> Self::Domain {
        Default::default()
    }
}

pub type FoldingAnalysisResults = monotone::AnalysisResults<FoldingAnalysis>;

impl FoldingAnalysisResults {
    pub fn compute(db: &dyn crate::Db, ib: &mir::ItemBody) -> Self {
        mono_analysis::<_, monotone::FiFo>(db, FoldingAnalysis, ib)
    }
}

pub struct FoldingAnalysis;

impl MonotoneFramework for FoldingAnalysis {
    type Domain = FoldingForrest;

    type Direction = monotone::Backward;

    fn semantic(
        &self,
        db: &dyn crate::Db,
        body: &mir::Body,
        act: mir::Action,
        prev: &mut Self::Domain,
    ) {
        prev.backwards_transition(db, body, act)
    }

    fn initial(&self, db: &dyn crate::Db, ib: &mir::ItemBody) -> Self::Domain {
        // TODO: We should look at params, return type, and post-conditions, to
        // see which locals should be folded at the exit
        let mut t = FoldingForrest::default();
        for &param in ib.params() {
            if param.ty(db, ib).is_ref(db) {
                t.require(db, None, RequireType::Folded, param.place(db, ib));
            }
        }
        t
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use tracing::{info, Level};

    use crate::{db::Database, file::SourceFile, mir, mono};

    fn generate_annotated_mir(src: &str) -> String {
        let db = Database::default();
        let file = SourceFile::new(&db, src.to_string());
        mono::monomorphized_items(&db, file)
            .items(&db)
            .iter()
            .filter_map(|&item| {
                info!("{}", item.name(&db));
                let span = tracing::span!(Level::DEBUG, "dump", item = item.name(&db).to_string());
                let _enter = span.enter();

                let ib = mir::lower_item(&db, item)?.ib(&db);

                let a = mir::analysis::liveness::FoldingAnalysisResults::compute(&db, ib);
                let serialized =
                    ib.serialize_with_annotation(&db, mir::serialize::Color::No, |act| {
                        let mut x = a.try_entry(act.loc())?.clone();
                        let incomming = x.debug_str(&db, ib);
                        x.forwards_transition(&db, ib, act.inner);
                        let outgoing = x.debug_str(&db, ib);
                        Some(format!("{incomming}\n> {outgoing}"))
                    });
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
          {%1_x: @}
        > {%1_x: @}
          !goto :B1
        :B1
          {%1_x: @}
        > {%1_x: X}
          %1_x := $12
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
          {%result: @, %1_x: @, %2: X}
        > {%result: @, %1_x: @, %2: X}
          !goto :B1
        :B1
          {%result: @, %1_x: @, %2: X}
        > {%result: @, %1_x: X, %2: X}
          %1_x := T { n: $12 }
          {%result: @, %1_x: { .n X }, %2: @}
        > {%result: @, %1_x: { .n X }, %2: X}
          %2 := (== %1_x.n $12)
          {%result: @, %1_x: X, %2: X}
        > {%result: @, %1_x: X, %2: X}
          assert %2 -> :B2
        :B2
          {%result: @, %1_x: X}
        > {%result: X, %1_x: X}
          %result := %1_x
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
          {%1_p: { .n X }, %2: @}
        > {%1_p: { .n X }, %2: @}
          !goto :B1
        :B1
          {%1_p: { .n X }, %2: @}
        > {%1_p: { .n X }, %2: X}
          %2 := (+ %1_p.n $1)
          {%1_p: { .n @ }, %2: X}
        > {%1_p: { .n X }, %2: X}
          %1_p.n := %2
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
          {%1_p: X}
        > {%1_p: X}
          !goto :B1
        :B1
          {%1_p: X}
        > {%1_p: { .t X }}
          %1_p.t := %1_p
          {%1_p: { .t X .n X }, %2: @}
        > {%1_p: { .t X .n X }, %2: X}
          %2 := (+ %1_p.n $1)
          {%1_p: { .t X .n @ }, %2: X}
        > {%1_p: { .t X .n X }, %2: X}
          %1_p.n := %2
          {%1_p: { .t { .n X } .n X }, %2: X}
        > {%1_p: { .t { .n X } .n X }, %2: X}
          %1_p.t.n := %1_p.n
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
          {%1_ts: @, %2: @, %3: @}
        > {%1_ts: @, %2: @, %3: @}
          !goto :B1
        :B1
          {%1_ts: @, %2: @, %3: @}
        > {%1_ts: @, %2: X, %3: @}
          %2 := T { n: $0 }
          {%1_ts: @, %2: X, %3: @}
        > {%1_ts: X, %2: X, %3: @}
          !call %1_ts := (#list %2) -> :B2
        :B2
          {%3: @}
        > {%3: X}
          %3 := $0
          {%1_ts: { [%3] { .n X } }, %3: @}
        > {%1_ts: { [%3] { .n X } }, %3: @}
          %1_ts[%3].n := $15
        "###)
    }
}
