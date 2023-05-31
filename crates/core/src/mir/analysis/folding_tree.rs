use itertools::Itertools;

use crate::{hir, mir, util::IdxMap};

use super::monotone::Lattice;

/// A [`FoldingTree`] maintains the the state of foldings and unfoldings of
/// [slots](crate::mir::Slot) and their projections.
#[derive(Default, Debug, Clone, Eq)]
pub struct FoldingTree {
    inner: IdxMap<mir::SlotId, folding_tree::FoldingTree<mir::ProjectionList>>,
}

impl PartialEq for FoldingTree {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
            || (self.inner.iter().all(|(slot, a_ft)| {
                if let Some(b_ft) = other.inner.get(slot) {
                    a_ft == b_ft
                } else {
                    a_ft.is_folded()
                }
            }) && other.inner.iter().all(|(slot, b_ft)| {
                if let Some(a_ft) = self.inner.get(slot) {
                    b_ft == a_ft
                } else {
                    b_ft.is_folded()
                }
            }))
    }
}

impl FoldingTree {
    pub fn debug_str(&self, db: Option<&dyn crate::Db>, body: &mir::Body) -> String {
        let entries = self
            .inner
            .iter()
            .map(|(slot, ft)| {
                let new_ft = ft.map_edges(|e| match body[e].last() {
                    Some(mir::Projection::Field(f, _)) => {
                        if let Some(db) = db {
                            format!(".{}", f.name(db))
                        } else {
                            format!(".?")
                        }
                    }
                    Some(mir::Projection::Index(idx, _)) => format!(
                        "[{}]",
                        mir::serialize::serialize_slot(mir::serialize::Color::No, None, body, *idx)
                    ),
                    None => "#".to_string(),
                });

                let slot =
                    mir::serialize::serialize_slot(mir::serialize::Color::No, None, body, slot);

                format!("{slot}: {new_ft}")
            })
            .format(", ");
        format!("{{{entries}}}")
    }
    /// Computes the nessesary foldings and unfoldings for the given place to be
    /// accessible.
    pub fn require(
        &mut self,
        body: &mir::Body,
        loc: Option<mir::BlockLocation>,
        place: mir::Place,
    ) -> Vec<mir::Folding> {
        // TODO: Potentially use the `loc` to determine locations where we
        // require something to be both folded and unfolded.
        let _ = loc;

        let mut foldings = vec![];

        let ft = self.inner.entry(place.slot).or_default();
        ft.require(
            |kind, path| {
                let p = if let Some(pl) = path.last() {
                    place.replace_projection(*pl)
                } else {
                    place.without_projection()
                };
                foldings.push(match kind {
                    folding_tree::EventKind::Unfold => mir::Folding::Unfold { consume: p },
                    folding_tree::EventKind::Fold => mir::Folding::Fold { into: p },
                })
            },
            body.projection_path_iter(place.projection).skip(1),
        );

        foldings
    }
    /// Erases all fold state for the given place and transitively for all
    /// children.
    ///
    /// This is useful when performing an assignment to a place, where all
    /// previous unfoldings into that place are lost.
    pub fn drop(&mut self, body: &mir::Body, place: mir::Place) {
        if let Some(ft) = self.inner.get_mut(place.slot) {
            ft.drop(body.projection_path_iter(place.projection).skip(1))
        }
    }

    pub fn compute_transition_into(&mut self, target: &FoldingTree) -> Vec<mir::Folding> {
        let mut foldings = vec![];
        for (slot, target_ft) in target.inner.iter() {
            self.inner.entry(slot).or_default().transition_into(
                |kind, path| {
                    let p = if let Some(&projection) = path.last() {
                        mir::Place { slot, projection }
                    } else {
                        slot.into()
                    };
                    foldings.push(match kind {
                        folding_tree::EventKind::Unfold => mir::Folding::Unfold { consume: p },
                        folding_tree::EventKind::Fold => mir::Folding::Fold { into: p },
                    })
                },
                target_ft,
            );
        }
        foldings
    }

    #[tracing::instrument(skip_all)]
    pub fn forwards_instruction_transition(&mut self, body: &mir::Body, inst: mir::InstructionId) {
        // debug!(inst=?&body[inst], "Starting with: {}", self.debug_str(None, body));
        for p in body[inst].places_referenced() {
            let _ = self.require(body, None, p);
        }
        for p in body[inst].places_written_to() {
            self.drop(body, p);
            let _ = self.require(body, None, p);
        }
        // debug!("Ending with:   {}", self.debug_str(None, body));
    }
    #[tracing::instrument(skip_all)]
    pub fn forwards_terminator_transition(
        &mut self,
        body: &mir::Body,
        terminator: &mir::Terminator,
    ) {
        // debug!(?terminator, "Starting with: {}", self.debug_str(None, body));
        for p in terminator.places_referenced() {
            let _ = self.require(body, None, p);
        }
        for p in terminator.places_written_to() {
            self.drop(body, p);
            let _ = self.require(body, None, p);
        }
        // debug!("Ending with:   {}", self.debug_str(None, body));
    }
    #[tracing::instrument(skip_all)]
    pub fn backwards_instruction_transition(&mut self, body: &mir::Body, inst: mir::InstructionId) {
        // debug!(inst=?&body[inst], "Starting with: {}", self.debug_str(None, body));
        for p in body[inst].places_written_to() {
            self.drop(body, p);
            let _ = self.require(body, None, p);
        }
        for p in body[inst].places_referenced() {
            let _ = self.require(body, None, p);
        }
        // debug!("Ending with:   {}", self.debug_str(None, body));
    }
    #[tracing::instrument(skip_all)]
    pub fn backwards_terminator_transition(
        &mut self,
        body: &mir::Body,
        terminator: &mir::Terminator,
    ) {
        // debug!(?terminator, "Starting with: {}", self.debug_str(None, body));
        for p in terminator.places_written_to() {
            self.drop(body, p);
            let _ = self.require(body, None, p);
        }
        for p in terminator.places_referenced() {
            let _ = self.require(body, None, p);
        }
        // debug!("Ending with:   {}", self.debug_str(None, body));
    }

    fn zip<'a, 'b>(
        &'a self,
        other: &'b FoldingTree,
    ) -> impl Iterator<
        Item = (
            mir::SlotId,
            Option<&'a folding_tree::FoldingTree<mir::ProjectionList>>,
            Option<&'b folding_tree::FoldingTree<mir::ProjectionList>>,
        ),
    > {
        self.inner
            .iter()
            .map(|(slot, a_ft)| (slot, Some(a_ft), other.inner.get(slot)))
            .chain(other.inner.iter().filter_map(|(slot, b_ft)| {
                if self.inner.contains_idx(slot) {
                    None
                } else {
                    Some((slot, None, Some(b_ft)))
                }
            }))
    }
}

impl Lattice<mir::Body> for FoldingTree {
    fn bottom(_body: &mir::Body) -> Self {
        Default::default()
    }

    #[tracing::instrument(skip_all)]
    fn lub(&self, _body: &mir::Body, other: &Self) -> Self {
        let inner = self
            .zip(other)
            .filter_map(|(slot, a_ft, b_ft)| {
                let new_ft = match (a_ft, b_ft) {
                    (Some(a_ft), Some(b_ft)) => a_ft.meet(b_ft),
                    (None, Some(x_ft)) | (Some(x_ft), None) => x_ft.clone(),
                    (None, None) => return None,
                };
                Some((slot, new_ft))
            })
            .collect();

        FoldingTree { inner }
    }

    #[tracing::instrument(skip_all)]
    fn contains(&self, _body: &mir::Body, other: &Self) -> bool {
        self.zip(other).all(|(_, a_ft, b_ft)| match (a_ft, b_ft) {
            (Some(a_ft), Some(b_ft)) => a_ft.contains(b_ft),
            (None, Some(_)) => false,
            (Some(_), None) => true,
            (None, None) => true,
        })
    }
}

#[allow(unused)]
pub(crate) fn debug_folding_tree(
    db: Option<&dyn crate::Db>,
    cx: Option<&hir::ItemContext>,
    body: &mir::Body,
    tree: &FoldingTree,
) -> String {
    tree.debug_str(db, body)
}

#[cfg(test)]
mod test {
    use std::{fmt, sync::Arc};

    use itertools::Itertools;
    use proptest::prelude::*;

    use crate::{hir, mir::Place};

    use super::*;

    #[derive(Clone)]
    struct Context {
        db: Arc<crate::db::Database>,
        cx: hir::ItemContext,
        body: mir::Body,
    }
    impl fmt::Debug for Context {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("Context").finish()
        }
    }

    prop_compose! {
        fn arb_ctx()(_x in any::<u8>()) -> Context {
            let db = crate::db::Database::default();

            let source = "
            struct P { a: P, b: P }

            fn f(x: P, y: P, z: P) {
                x;
                x.a;
                x.a.a;
                x.a.a.a;
                x.b;
                x.b.a;
                x.b.a.a;
                x.a.b;
                x.a.b.a;
                x.b.b;
                x.b.b.a;
                x.a.a.b;
                x.b.a.b;
                x.a.b.b;
                x.b.b.b;
            }";
            let file = hir::SourceFile::new(&db, source.to_string());
            let def = hir::file_definitions(&db, file).into_iter().nth(1).unwrap();
            let (cx, body) = def.hir_mir(&db).unwrap();
            let (cx, body) = (cx.clone(), body.clone());

            Context { db: Arc::new(db), cx, body }
        }
    }
    fn debug_folding_tree_ctx(ctx: &Context, tree: &FoldingTree) -> String {
        debug_folding_tree(Some(&*ctx.db), Some(&ctx.cx), &ctx.body, tree)
    }

    struct Input {
        ctx: Context,
        trees: Vec<FoldingTree>,
    }
    impl fmt::Debug for Input {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let mut f = f.debug_tuple("Input");
            for t in &self.trees {
                f.field(&debug_folding_tree_ctx(&self.ctx, t));
            }
            f.finish()
        }
    }
    prop_compose! {
        fn arb_place(ctx: &Context)
            (slot in prop::sample::select(ctx.body.slots.idxs().collect_vec()),
             projection in prop::sample::select(ctx.body.projections.idxs().collect_vec()))
            -> Place
        {
            Place { slot, projection }
        }
    }
    prop_compose! {
        fn arb_folding_tree(ctx: Context)
            (places in prop::collection::vec(arb_place(&ctx), 0..10))
            -> FoldingTree
        {
            let mut tree = FoldingTree::default();
            for p in places {
                let _ = tree.require(&ctx.body, None, p);
            }
            tree
        }
    }
    prop_compose! {
        fn arb_ctx_trees(n: usize)(ctx in arb_ctx())
                             (trees in prop::collection::vec(arb_folding_tree(ctx.clone()), n..=n),
                              ctx in Just(ctx))
                             -> Input
        {
            Input { ctx, trees }
        }
    }
    proptest! {
        #[test]
        fn folding_tree_lattice_lub_idempotent(Input { ctx, trees } in arb_ctx_trees(1)) {
            let [tree]: [_; 1] = trees.try_into().unwrap();
            let lub = tree.lub(&ctx.body, &tree);
            prop_assert!(
                lub == tree,
                "{} != {}",
                debug_folding_tree_ctx(&ctx, &lub),
                debug_folding_tree_ctx(&ctx, &tree),
            );
        }
    }
    proptest! {
        #[test]
        fn folding_tree_lattice_lub_identity(Input { ctx, trees } in arb_ctx_trees(1)) {
            let [tree]: [_; 1] = trees.try_into().unwrap();
            let lub_1 = tree.lub(&ctx.body, &FoldingTree::default());
            let lub_2 = FoldingTree::default().lub(&ctx.body, &tree);
            prop_assert!(
                lub_1 == tree,
                "{} != {}",
                debug_folding_tree_ctx(&ctx, &lub_1),
                debug_folding_tree_ctx(&ctx, &tree),
            );
            prop_assert!(
                lub_2 == tree,
                "{} != {}",
                debug_folding_tree_ctx(&ctx, &lub_2),
                debug_folding_tree_ctx(&ctx, &tree),
            );
        }
    }

    proptest! {
        #[test]
        fn folding_tree_lattice_commute(Input { ctx, trees } in arb_ctx_trees(2)) {
            let [lhs, rhs]: [_; 2] = trees.try_into().unwrap();
            let lub_lr = lhs.lub(&ctx.body, &rhs);
            let lub_rl = rhs.lub(&ctx.body, &lhs);

            eprintln!(
                "lub({}, {}) = {}",
                debug_folding_tree_ctx(&ctx, &lhs),
                debug_folding_tree_ctx(&ctx, &rhs),
                debug_folding_tree_ctx(&ctx, &lub_lr),
            );
            eprintln!(
                "lub({}, {}) = {}",
                debug_folding_tree_ctx(&ctx, &rhs),
                debug_folding_tree_ctx(&ctx, &lhs),
                debug_folding_tree_ctx(&ctx, &lub_rl),
            );

            prop_assert!(
                lub_lr == lub_rl,
                "{} != {}",
                debug_folding_tree_ctx(&ctx, &lub_lr),
                debug_folding_tree_ctx(&ctx, &lub_rl),
            );
        }
    }

    proptest! {
        #[test]
        fn folding_tree_lattice_commute_3(Input { ctx, trees } in arb_ctx_trees(3)) {
            let [a, b, c]: [_; 3] = trees.try_into().unwrap();

            let cases = [a, b, c]
                .into_iter()
                .permutations(3)
                .map(|ts| ts[0].lub(&ctx.body, &ts[1].lub(&ctx.body, &ts[2])))
                .collect_vec();

            for (x, y) in cases.iter().tuple_windows() {
                prop_assert!(
                    x == y,
                    "{} != {}",
                    debug_folding_tree_ctx(&ctx, x),
                    debug_folding_tree_ctx(&ctx, y),
                );
            }

        }
    }

    proptest! {
        #[test]
        fn folding_tree_lattice_assoc(Input { ctx, trees } in arb_ctx_trees(3)) {
            let [a, b, c]: [_; 3] = trees.try_into().unwrap();

            let cases = [a, b, c]
                .into_iter()
                .permutations(3)
                .map(|ts| (
                    ts[0].lub(&ctx.body, &ts[1].lub(&ctx.body, &ts[2])),
                    ts[0].lub(&ctx.body, &ts[1]).lub(&ctx.body, &ts[2]),
                ))
                .collect_vec();

            for (x, y) in cases.iter() {
                prop_assert!(
                    x == y,
                    "{} != {}",
                    debug_folding_tree_ctx(&ctx, x),
                    debug_folding_tree_ctx(&ctx, y),
                );
            }

        }
    }

    proptest! {
        #[test]
        fn folding_tree_lattice_lub_2(Input { ctx, trees } in arb_ctx_trees(2)) {
            let [lhs, rhs]: [_; 2] = trees.try_into().unwrap();
            let lub = lhs.lub(&ctx.body, &rhs);

            eprintln!(
                "lub({}, {}) = {}",
                debug_folding_tree_ctx(&ctx, &lhs),
                debug_folding_tree_ctx(&ctx, &rhs),
                debug_folding_tree_ctx(&ctx, &lub),
            );

            // ⋢
            // ⋣

            prop_assert!(
                lub.contains(&ctx.body, &lhs),
                "{} ⋣ {}",
                debug_folding_tree_ctx(&ctx, &lub),
                debug_folding_tree_ctx(&ctx, &lhs),
            );
            prop_assert!(
                lub.contains(&ctx.body, &rhs),
                "{} ⋣ {}",
                debug_folding_tree_ctx(&ctx, &lub),
                debug_folding_tree_ctx(&ctx, &rhs),
            );
        }
    }

    proptest! {
        #[test]
        fn folding_tree_lattice_lub_3(Input { ctx, trees } in arb_ctx_trees(3)) {
            let [a, b, c]: [_; 3] = trees.try_into().unwrap();

            let cases = [a, b, c]
                .into_iter()
                .permutations(3)
                .map(|ts| {
                    let lub = ts[0].lub(&ctx.body, &ts[1]).lub(&ctx.body, &ts[2]);
                    (ts, lub)
                })
                .collect_vec();

            for (ts, lub) in cases.iter() {
                for t in ts {
                    prop_assert!(
                        lub.contains(&ctx.body, t),
                        "{} ⋣ {}",
                        debug_folding_tree_ctx(&ctx, lub),
                        debug_folding_tree_ctx(&ctx, t),
                    );
                }
            }
        }
    }
}
