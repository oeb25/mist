use std::{
    collections::{HashMap, HashSet},
    iter,
};

use tracing::warn;

use crate::{hir, mir};

use super::monotone::Lattice;

#[derive(Debug, Clone, PartialEq, Eq)]
enum FoldingNode {
    Unfolded { children: HashSet<mir::Place> },
    Folded,
}

impl Default for FoldingNode {
    fn default() -> Self {
        FoldingNode::Unfolded {
            children: HashSet::new(),
        }
    }
}

/// A [`FoldingTree`] maintains the the state of foldings and unfoldings of
/// [slots](crate::mir::Slot) and their projections.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct FoldingTree {
    nodes: HashMap<mir::Place, (Option<mir::BlockLocation>, FoldingNode)>,
}

impl FoldingTree {
    pub fn leafs(&self) -> impl Iterator<Item = mir::Place> + '_ {
        self.nodes.iter().filter_map(|(k, (_, v))| match v {
            FoldingNode::Folded => Some(*k),
            FoldingNode::Unfolded { .. } => None,
        })
    }
    /// Computes the nessesary foldings and unfoldings for the given place to be
    /// accessible.
    pub fn require(
        &mut self,
        body: &mir::Body,
        loc: Option<mir::BlockLocation>,
        place: mir::Place,
    ) -> Vec<mir::Folding> {
        let mut foldings = vec![];

        match self.nodes.insert(place, (loc, FoldingNode::Folded)) {
            Some((prev_loc, FoldingNode::Folded)) => {
                // NOTE: Already folded, nothing to do
                if prev_loc.is_some() && loc == prev_loc {
                    warn!("unfolding something that was folded at same loc");
                }
            }
            Some((_, FoldingNode::Unfolded { children })) => {
                // NOTE: Was unfolded, need to fold children
                for child in children {
                    foldings.extend(self.require(body, loc, child));
                    self.nodes.remove(&child);
                }
                foldings.push(mir::Folding::Fold {
                    consume: vec![],
                    into: place,
                });
            }
            None => {
                if let Some(parent) = place.parent(body) {
                    // NOTE: Need to unfold parent
                    if let Some((_, FoldingNode::Unfolded { children })) =
                        self.nodes.get_mut(&parent)
                    {
                        children.insert(place);
                    } else {
                        foldings.extend(self.require(body, loc, parent));
                        match self.nodes.get_mut(&parent) {
                            Some((_, folding @ FoldingNode::Folded)) => {
                                *folding = FoldingNode::Unfolded {
                                    children: [place].into_iter().collect(),
                                };
                                foldings.push(mir::Folding::Unfold {
                                    consume: parent,
                                    into: vec![],
                                });
                            }
                            x => todo!("{x:?}"),
                        }
                    }
                } else {
                    // NOTE: At root, so all done
                }
            }
        }

        foldings
    }
    /// Erases all fold state for the given place and transitively for all
    /// children.
    ///
    /// This is useful when performing an assignment to a place, where all
    /// previous unfoldings into that place are lost.
    pub fn drop(&mut self, place: mir::Place) {
        let mut drop_queue = vec![place];
        while let Some(place) = drop_queue.pop() {
            match self.nodes.remove(&place) {
                None | Some((_, FoldingNode::Folded)) => {}
                Some((_, FoldingNode::Unfolded { children })) => {
                    drop_queue.extend(children);
                }
            }
        }
    }

    pub fn compute_transition_into(
        &mut self,
        body: &mir::Body,
        target: &FoldingTree,
    ) -> Vec<mir::Folding> {
        target
            .leafs()
            .flat_map(|k| self.require(body, None, k))
            .collect()
    }

    pub fn forwards_instruction_transition(&mut self, body: &mir::Body, inst: mir::InstructionId) {
        for p in body[inst].places_referenced() {
            let _ = self.require(body, None, p);
        }
        for p in body[inst].places_written_to() {
            self.drop(p);
            let _ = self.require(body, None, p);
        }
    }
    pub fn forwards_terminator_transition(
        &mut self,
        body: &mir::Body,
        terminator: &mir::Terminator,
    ) {
        for p in terminator.places_referenced() {
            let _ = self.require(body, None, p);
        }
        for p in terminator.places_written_to() {
            self.drop(p);
            let _ = self.require(body, None, p);
        }
    }
    pub fn backwards_instruction_transition(&mut self, body: &mir::Body, inst: mir::InstructionId) {
        for p in body[inst].places_written_to() {
            self.drop(p);
            let _ = self.require(body, None, p);
        }
        for p in body[inst].places_referenced() {
            let _ = self.require(body, None, p);
        }
    }
    pub fn backwards_terminator_transition(
        &mut self,
        body: &mir::Body,
        terminator: &mir::Terminator,
    ) {
        for p in terminator.places_written_to() {
            self.drop(p);
            let _ = self.require(body, None, p);
        }
        for p in terminator.places_referenced() {
            let _ = self.require(body, None, p);
        }
    }
}

impl Lattice<mir::Body> for FoldingTree {
    fn bottom(_body: &mir::Body) -> Self {
        Default::default()
    }

    fn lub(&self, body: &mir::Body, other: &Self) -> Self {
        let mut new = FoldingTree::default();
        for p1 in self.leafs() {
            if !other.leafs().any(|p2| {
                iter::successors(p1.parent(body), |p1| p1.parent(body)).any(|p1| p1 == p2)
            }) {
                let _ = new.require(body, None, p1);
            }
        }
        for p1 in other.leafs() {
            if !self.leafs().any(|p2| {
                iter::successors(p1.parent(body), |p1| p1.parent(body)).any(|p1| p1 == p2)
            }) {
                let _ = new.require(body, None, p1);
            }
        }
        new
    }

    fn contains(&self, body: &mir::Body, other: &Self) -> bool {
        other.leafs().all(|p1| {
            self.leafs().any(|p2| p1 == p2)
                || iter::successors(p1.parent(body), |p1| p1.parent(body))
                    .any(|p1| self.leafs().any(|p2| p1 == p2))
        })
    }
}

#[allow(unused)]
pub(crate) fn debug_folding_tree(
    cx: Option<&hir::ItemContext>,
    body: &mir::Body,
    tree: &FoldingTree,
) -> HashSet<String> {
    tree.leafs()
        .map(|p| mir::serialize::serialize_place(mir::serialize::Color::No, cx, body, &p))
        .collect::<std::collections::HashSet<_>>()
}

#[cfg(test)]
mod test {
    use std::{fmt, sync::Arc};

    use itertools::Itertools;
    use proptest::prelude::*;

    use crate::{hir, mir::Place};

    use super::*;

    #[derive(Debug, PartialEq, Eq)]
    enum InvariantError {
        ChildrenEmpty,
        ChildMissing,
        ParentDoesNotContainChild,
        ParentMissing,
        ParentFolded,
    }

    impl FoldingTree {
        fn invariant(&self, body: &mir::Body) -> Result<(), InvariantError> {
            for (p, (_, folding)) in &self.nodes {
                match folding {
                    FoldingNode::Unfolded { children } => {
                        if children.is_empty() {
                            return Err(InvariantError::ChildrenEmpty);
                        }
                        for child in children {
                            if !self.nodes.contains_key(child) {
                                return Err(InvariantError::ChildMissing);
                            }
                        }
                    }
                    FoldingNode::Folded => {
                        if let Some(parent) = p.parent(body) {
                            if let Some((_, parent_folding)) = self.nodes.get(&parent) {
                                match parent_folding {
                                    FoldingNode::Unfolded { children } => {
                                        if !children.contains(p) {
                                            return Err(InvariantError::ParentDoesNotContainChild);
                                        }
                                    }
                                    FoldingNode::Folded => {
                                        return Err(InvariantError::ParentFolded)
                                    }
                                }
                            } else {
                                return Err(InvariantError::ParentMissing);
                            }
                        }
                    }
                }
            }

            Ok(())
        }
    }

    #[derive(Clone)]
    struct Context {
        _db: Arc<crate::db::Database>,
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
            let source = hir::SourceProgram::new(&db, source.to_string());
            let program = hir::parse_program(&db, source);
            let (_, cx, _, body, _) =
                mir::lower_program(&db, program).into_iter().nth(1).unwrap();

            Context { _db: Arc::new(db), cx, body }
        }
    }
    fn debug_folding_tree_ctx(ctx: &Context, tree: &FoldingTree) -> HashSet<String> {
        debug_folding_tree(Some(&ctx.cx), &ctx.body, tree)
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
            dbg!(&tree);
            dbg!(&lub);
            prop_assert!(
                lub == tree,
                "{:?} != {:?}",
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
                "{:?} != {:?}",
                debug_folding_tree_ctx(&ctx, &lub_1),
                debug_folding_tree_ctx(&ctx, &tree),
            );
            prop_assert!(
                lub_2 == tree,
                "{:?} != {:?}",
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

            dbg!(&lhs);
            dbg!(&rhs);
            dbg!(&lub_lr);
            dbg!(&lub_rl);

            eprintln!(
                "lub({:?}, {:?}) = {:?}",
                debug_folding_tree_ctx(&ctx, &lhs),
                debug_folding_tree_ctx(&ctx, &rhs),
                debug_folding_tree_ctx(&ctx, &lub_lr),
            );
            eprintln!(
                "lub({:?}, {:?}) = {:?}",
                debug_folding_tree_ctx(&ctx, &rhs),
                debug_folding_tree_ctx(&ctx, &lhs),
                debug_folding_tree_ctx(&ctx, &lub_rl),
            );

            prop_assert!(
                lub_lr == lub_rl,
                "{:?} != {:?}",
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
                dbg!(x);
                dbg!(y);
                prop_assert!(
                    x == y,
                    "{:?} != {:?}",
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
                dbg!(x);
                dbg!(y);
                prop_assert!(
                    x == y,
                    "{:?} != {:?}",
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
                "lub({:?}, {:?}) = {:?}",
                debug_folding_tree_ctx(&ctx, &lhs),
                debug_folding_tree_ctx(&ctx, &rhs),
                debug_folding_tree_ctx(&ctx, &lub),
            );

            // ⋢
            // ⋣

            prop_assert!(
                lub.contains(&ctx.body, &lhs),
                "{:?} ⋣ {:?}",
                debug_folding_tree_ctx(&ctx, &lub),
                debug_folding_tree_ctx(&ctx, &lhs),
            );
            prop_assert!(
                lub.contains(&ctx.body, &rhs),
                "{:?} ⋣ {:?}",
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
                        "{:?} ⋣ {:?}",
                        debug_folding_tree_ctx(&ctx, lub),
                        debug_folding_tree_ctx(&ctx, t),
                    );
                }
            }
        }
    }

    proptest! {
        #[test]
        fn folding_tree_lattice_invariant(Input { ctx, trees } in arb_ctx_trees(1)) {
            let [tree]: [_; 1] = trees.try_into().unwrap();
            dbg!(&tree);
            prop_assert_eq!(tree.invariant(&ctx.body), Ok(()));
        }
    }

    proptest! {
        #[test]
        fn folding_tree_lattice_lub_invariant(Input { ctx, trees } in arb_ctx_trees(3)) {
            let [a, b, c]: [_; 3] = trees.try_into().unwrap();

            let cases = [a, b, c].into_iter().permutations(3);

            for ts in cases {
                for t in &ts {
                    dbg!(t);
                    prop_assert_eq!(t.invariant(&ctx.body), Ok(()));
                }
                let lub = ts[0].lub(&ctx.body, &ts[1]).lub(&ctx.body, &ts[2]);
                prop_assert_eq!(lub.invariant(&ctx.body), Ok(()));
            }
        }
    }
}