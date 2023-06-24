use folding_tree::{FoldingTree, RequireType};
use itertools::Itertools;

use crate::{mir, util::IdxMap};

use super::monotone::Lattice;

/// A [`FoldingForrest`] maintains the the state of foldings and unfoldings of
/// [slots](crate::mir::Slot) and their projections.
#[derive(Default, Debug, Clone, Eq)]
pub struct FoldingForrest {
    inner: IdxMap<mir::SlotId, FoldingTree<mir::ProjectionList>>,
}

impl PartialEq for FoldingForrest {
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

impl FoldingForrest {
    pub fn debug_str(&self, db: &dyn crate::Db, body: &mir::Body) -> String {
        let entries = self
            .inner
            .iter()
            .map(|(slot, ft)| {
                let new_ft = ft.map_edges(|e| match e.last(db) {
                    Some(mir::Projection::Field(f, _)) => {
                        format!(".{}", f.name(db))
                    }
                    Some(mir::Projection::Index(idx, _)) => format!(
                        "[{}]",
                        mir::serialize::serialize_slot(mir::serialize::Color::No, db, body, idx)
                    ),
                    None => "#".to_string(),
                });

                let slot =
                    mir::serialize::serialize_slot(mir::serialize::Color::No, db, body, slot);

                format!("{slot}: {new_ft}")
            })
            .format(", ");
        format!("{{{entries}}}")
    }
    /// Computes the nessesary foldings and unfoldings for the given place to be
    /// accessible.
    pub fn require(
        &mut self,
        db: &dyn crate::Db,
        loc: Option<mir::BlockLocation>,
        req_ty: RequireType,
        place: mir::Place,
    ) -> Vec<mir::Folding> {
        // TODO: Potentially use the `loc` to determine locations where we
        // require something to be both folded and unfolded.
        let _ = loc;

        let mut foldings = vec![];

        let ft = self.inner.entry(place.slot()).or_default();
        ft.soft_require(
            |kind, path| {
                let p = if let Some(pl) = path.last() {
                    place.replace_projection(db, *pl)
                } else {
                    place.without_projection(db)
                };
                foldings.push(match kind {
                    folding_tree::EventKind::Unfold => mir::Folding::Unfold { consume: p },
                    folding_tree::EventKind::Fold => mir::Folding::Fold { into: p },
                })
            },
            req_ty,
            place.projection_path_iter(db).skip(1),
        );

        foldings
    }
    /// Erases all fold state for the given place and transitively for all
    /// children.
    ///
    /// This is useful when performing an assignment to a place, where all
    /// previous unfoldings into that place are lost.
    pub fn drop(&mut self, db: &dyn crate::Db, place: mir::Place) {
        if let Some(ft) = self.inner.get_mut(place.slot()) {
            ft.drop(place.projection_path_iter(db).skip(1))
        }
    }

    pub fn compute_transition_into(
        &mut self,
        db: &dyn crate::Db,
        body: &mir::Body,
        target: &FoldingForrest,
    ) -> Vec<mir::Folding> {
        let mut foldings = vec![];
        for (slot, target_ft) in target.inner.iter() {
            self.inner.entry(slot).or_default().transition_into(
                |kind, path| {
                    let p = if let Some(&projection) = path.last() {
                        slot.place(db, body).replace_projection(db, projection)
                    } else {
                        slot.place(db, body)
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

    pub fn forwards_transition(&mut self, db: &dyn crate::Db, body: &mir::Body, act: mir::Action) {
        match act {
            mir::Action::Instruction(inst) => match inst.data(body) {
                mir::Instruction::Folding(f) => match f {
                    mir::Folding::Fold { into } => {
                        self.fold(db, *into);
                    }
                    mir::Folding::Unfold { consume } => {
                        self.unfold(db, *consume);
                    }
                },
                _ => {
                    for p in inst.places_referenced(db, body) {
                        let _ = self.require(db, None, RequireType::Folded, p);
                    }
                    for p in inst.places_written_to(body) {
                        self.drop(db, p);
                        let _ = self.require(db, None, RequireType::Folded, p);
                    }
                }
            },
            mir::Action::Terminator(t) => {
                for p in t.places_referenced(db) {
                    let _ = self.require(db, None, RequireType::Folded, p);
                }
                for p in t.places_written_to(db) {
                    self.drop(db, p);
                    let _ = self.require(db, None, RequireType::Folded, p);
                }
            }
        }
    }
    pub fn backwards_transition(&mut self, db: &dyn crate::Db, body: &mir::Body, act: mir::Action) {
        match act {
            mir::Action::Instruction(inst) => match inst.data(body) {
                mir::Instruction::Folding(f) => match f {
                    mir::Folding::Fold { into } => {
                        self.unfold(db, *into);
                    }
                    mir::Folding::Unfold { consume } => {
                        self.fold(db, *consume);
                    }
                },
                _ => {
                    for p in inst.places_written_to(body) {
                        self.drop(db, p);
                        self.require(db, None, RequireType::Accessible, p);
                    }
                    for p in inst.places_referenced(db, body) {
                        let _ = self.require(db, None, RequireType::Folded, p);
                    }
                }
            },
            mir::Action::Terminator(t) => {
                for p in t.places_written_to(db) {
                    self.drop(db, p);
                    self.require(db, None, RequireType::Accessible, p);
                }
                for p in t.places_referenced(db) {
                    let _ = self.require(db, None, RequireType::Folded, p);
                }
            }
        }
    }

    fn zip<'a, 'b>(
        &'a self,
        other: &'b FoldingForrest,
    ) -> impl Iterator<
        Item = (
            mir::SlotId,
            Option<&'a FoldingTree<mir::ProjectionList>>,
            Option<&'b FoldingTree<mir::ProjectionList>>,
        ),
    > {
        self.inner.iter().map(|(slot, a_ft)| (slot, Some(a_ft), other.inner.get(slot))).chain(
            other.inner.iter().filter_map(|(slot, b_ft)| {
                if self.inner.contains_idx(slot) {
                    None
                } else {
                    Some((slot, None, Some(b_ft)))
                }
            }),
        )
    }

    fn fold(&mut self, db: &dyn crate::Db, p: mir::Place) {
        let ft = self.inner.entry(p.slot()).or_default();
        // TODO: Perhaps we should check that these are valid
        let _ = ft.fold(p.projection_path_iter(db).skip(1));
    }
    fn unfold(&mut self, db: &dyn crate::Db, p: mir::Place) {
        let ft = self.inner.entry(p.slot()).or_default();
        // TODO: Perhaps we should check that these are valid
        let _ = ft.unfold(p.projection_path_iter(db).skip(1));
    }
}

impl<T> Lattice<T> for FoldingForrest {
    fn bottom(_body: &T) -> Self {
        Default::default()
    }

    fn lub(&self, _body: &T, other: &Self) -> Self {
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

        FoldingForrest { inner }
    }

    fn contains(&self, _body: &T, other: &Self) -> bool {
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
    db: &dyn crate::Db,
    body: &mir::Body,
    tree: &FoldingForrest,
) -> String {
    tree.debug_str(db, body)
}

#[cfg(test)]
mod test {
    use std::{fmt, sync::Arc};

    use itertools::Itertools;
    use proptest::prelude::*;

    use crate::{
        file::SourceFile,
        mir::{Place, Projection, ProjectionList},
        mono::{self, exprs::Field, types::Adt, Item},
    };

    use super::*;

    #[derive(Clone)]
    struct Context {
        db: Arc<crate::db::Database>,
        items: Vec<Item>,
        ib: mir::ItemBody,
    }
    impl fmt::Debug for Context {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.debug_struct("Context").finish()
        }
    }
    impl Context {
        fn db(&self) -> &dyn crate::Db {
            &*self.db
        }
        fn body(&self) -> &mir::Body {
            &self.ib
        }
        fn adts(&self) -> Vec<Adt> {
            self.items
                .iter()
                .filter_map(|item| match item.kind(self.db()) {
                    mono::ItemKind::Adt(adt) => Some(adt),
                    mono::ItemKind::Function(_) => None,
                })
                .collect()
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
            let file = SourceFile::new(&db, source.to_string());
            let mono = mono::monomorphized_items(&db, file);
            let items = mono.items(&db);
            let item = items[1];
            let ib = mir::lower_item(&db, item).unwrap().ib(&db).clone();

            Context { db: Arc::new(db), items, ib }
        }
    }
    fn debug_folding_tree_ctx(ctx: &Context, tree: &FoldingForrest) -> String {
        debug_folding_tree(ctx.db(), ctx.body(), tree)
    }

    struct Input {
        ctx: Context,
        trees: Vec<FoldingForrest>,
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
        fn arb_adt(ctx: Context)(adt in prop::sample::select(ctx.adts())) -> Adt
        { adt }
    }
    prop_compose! {
        fn arb_projection(ctx: Context)
            (adt in arb_adt(ctx.clone()),
             ctx in Just(ctx)
            )
            (field in prop::sample::select(adt.fields(ctx.db())),
             adt in Just(adt),
             ctx in Just(ctx))
            -> Projection
        {
            Projection::Field(Field::AdtField(adt, field), field.ty(ctx.db()))
        }
    }
    prop_compose! {
        fn arb_projection_list(ctx: Context)
            (projections in prop::collection::vec(arb_projection(ctx.clone()), 0..10))
            -> ProjectionList
        {
            ProjectionList::new(ctx.db(), projections)
        }
    }
    prop_compose! {
        fn arb_place(ctx: Context)
            (slot in prop::sample::select(ctx.body().slots().collect_vec()),
             projection in arb_projection_list(ctx.clone()),
             ctx in Just(ctx)
            )
            -> Place
        {
            slot.place(ctx.db(), ctx.body()).replace_projection(ctx.db(), projection)
        }
    }
    prop_compose! {
        fn arb_folding_tree(ctx: Context)
            (places in prop::collection::vec(arb_place(ctx.clone()), 0..10))
            -> FoldingForrest
        {
            let mut tree = FoldingForrest::default();
            for p in places {
                let _ = tree.require(ctx.db(), None, RequireType::Folded, p);
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
            let lub = tree.lub(ctx.body(), &tree);
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
            let lub_1 = tree.lub(ctx.body(), &FoldingForrest::default());
            let lub_2 = FoldingForrest::default().lub(ctx.body(), &tree);
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
            let lub_lr = lhs.lub(ctx.body(), &rhs);
            let lub_rl = rhs.lub(ctx.body(), &lhs);

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
                .map(|ts| ts[0].lub(ctx.body(), &ts[1].lub(ctx.body(), &ts[2])))
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
                    ts[0].lub(ctx.body(), &ts[1].lub(ctx.body(), &ts[2])),
                    ts[0].lub(ctx.body(), &ts[1]).lub(ctx.body(), &ts[2]),
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
            let lub = lhs.lub(ctx.body(), &rhs);

            eprintln!(
                "lub({}, {}) = {}",
                debug_folding_tree_ctx(&ctx, &lhs),
                debug_folding_tree_ctx(&ctx, &rhs),
                debug_folding_tree_ctx(&ctx, &lub),
            );

            // ⋢
            // ⋣

            prop_assert!(
                lub.contains(ctx.body(), &lhs),
                "{} ⋣ {}",
                debug_folding_tree_ctx(&ctx, &lub),
                debug_folding_tree_ctx(&ctx, &lhs),
            );
            prop_assert!(
                lub.contains(ctx.body(), &rhs),
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
                    let lub = ts[0].lub(ctx.body(), &ts[1]).lub(ctx.body(), &ts[2]);
                    (ts, lub)
                })
                .collect_vec();

            for (ts, lub) in cases.iter() {
                for t in ts {
                    prop_assert!(
                        lub.contains(ctx.body(), t),
                        "{} ⋣ {}",
                        debug_folding_tree_ctx(&ctx, lub),
                        debug_folding_tree_ctx(&ctx, t),
                    );
                }
            }
        }
    }
}
