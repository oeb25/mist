use std::{fmt, hash::Hash};

use indexmap::{map::Entry, IndexMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Folding {
    Folded,
    Unfolded,
}

impl Folding {
    /// Returns `true` if the folding is [`Folded`].
    ///
    /// [`Folded`]: Folding::Folded
    #[must_use]
    fn is_folded(&self) -> bool {
        matches!(self, Self::Folded)
    }

    /// Returns `true` if the folding is [`Unfolded`].
    ///
    /// [`Unfolded`]: Folding::Unfolded
    #[must_use]
    fn is_unfolded(&self) -> bool {
        matches!(self, Self::Unfolded)
    }
}

#[derive(Debug)]
pub struct FoldingTree<E> {
    nodes: Vec<Folding>,
    children: Vec<IndexMap<E, usize>>,
}

impl<E: fmt::Display> fmt::Display for FoldingTree<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn print_node<E: fmt::Display>(
            ft: &FoldingTree<E>,
            edge: Option<&E>,
            idx: usize,
            f: &mut fmt::Formatter<'_>,
        ) -> fmt::Result {
            if let Some(edge) = edge {
                write!(f, "{edge} ")?
            }
            match ft.nodes[idx] {
                Folding::Folded => write!(f, "X"),
                Folding::Unfolded => {
                    write!(f, "{{ ")?;
                    for (edge, idx) in &ft.children[idx] {
                        print_node(ft, Some(edge), *idx, f)?;
                        write!(f, " ")?;
                    }
                    write!(f, "}}")
                }
            }
        }

        print_node(self, None, 0, f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EventKind {
    Unfold,
    Fold,
}

impl<E> FoldingTree<E> {
    pub fn require(
        &mut self,
        mut events: impl for<'a> FnMut(EventKind, &'a [E]),
        path: impl IntoIterator<Item = E>,
    ) where
        E: PartialEq + Eq + Hash + Clone,
    {
        use Folding::*;

        let mut current_idx = 0;
        let mut current_path = Vec::new();

        for edge in path {
            let next_idx = self.next_idx();
            let children = &mut self.children[current_idx];
            if self.nodes[current_idx].is_folded() {
                events(EventKind::Unfold, &current_path);
            }
            self.nodes[current_idx] = Unfolded;

            current_idx = match children.entry(edge.clone()) {
                Entry::Occupied(it) => *it.get(),
                Entry::Vacant(it) => {
                    it.insert(next_idx);
                    self.alloc_folded()
                }
            };

            current_path.push(edge);
        }

        if self.nodes[current_idx].is_folded() {
            return;
        }

        let mut folding_stack = vec![(current_idx, current_path.len(), None)];

        while let Some((idx, n, edge)) = folding_stack.pop() {
            current_path.truncate(n);
            if let Some(edge) = edge.clone() {
                current_path.push(edge);
            }
            if self.nodes[idx].is_folded() {
                continue;
            }
            if self.children[idx]
                .iter()
                .all(|(_, &child_idx)| self.nodes[child_idx].is_folded())
            {
                self.nodes[idx] = Folded;
                events(EventKind::Fold, &current_path);
                continue;
            }
            folding_stack.push((idx, n, edge));
            folding_stack.extend(
                self.children[idx]
                    .iter()
                    .map(|(e, idx)| (*idx, current_path.len(), Some(e.clone()))),
            );
        }
    }

    #[must_use]
    pub fn meet(&self, other: &FoldingTree<E>) -> FoldingTree<E>
    where
        E: PartialEq + Eq + Hash + Clone,
    {
        use Folding::*;

        let mut m = FoldingTree::default();

        let mut queue = vec![(0, 0, 0)];

        while let Some((m_idx, a_idx, b_idx)) = queue.pop() {
            if self.nodes[a_idx].is_unfolded() && other.nodes[b_idx].is_unfolded() {
                m.nodes[m_idx] = Unfolded;

                for (edge, a_child) in &self.children[a_idx] {
                    if let Some(b_child) = other.children[b_idx].get(edge) {
                        let m_child = m.alloc_folded();
                        m.children[m_idx].insert(edge.clone(), m_child);

                        queue.push((m_child, *a_child, *b_child));
                    }
                }

                for (edge, b_child) in &other.children[b_idx] {
                    if let Some(a_child) = self.children[a_idx].get(edge) {
                        if m.children[m_idx].contains_key(edge) {
                            continue;
                        }

                        let m_child = m.alloc_folded();
                        m.children[m_idx].insert(edge.clone(), m_child);

                        queue.push((m_child, *a_child, *b_child));
                    }
                }
            }
        }

        m
    }
}

impl<E> FoldingTree<E> {
    fn next_idx(&self) -> usize {
        self.nodes.len()
    }
    fn alloc_folded(&mut self) -> usize {
        let idx = self.nodes.len();
        self.nodes.push(Folding::Folded);
        self.children.push(IndexMap::default());
        idx
    }
}

impl<E> PartialEq for FoldingTree<E>
where
    E: PartialEq + Eq + Hash,
{
    fn eq(&self, other: &Self) -> bool {
        use Folding::*;

        let mut queue = vec![(0, 0)];

        while let Some((a_idx, b_idx)) = queue.pop() {
            match (self.nodes[a_idx], other.nodes[b_idx]) {
                (Folded, Folded) => {}
                (Unfolded, Unfolded) => {
                    for (edge, &a_child) in &self.children[a_idx] {
                        if let Some(&b_child) = other.children[b_idx].get(edge) {
                            if !queue.contains(&(a_child, b_child)) {
                                queue.push((a_child, b_child));
                            }
                        }
                    }

                    for (edge, &b_child) in &other.children[b_idx] {
                        if let Some(&a_child) = self.children[a_idx].get(edge) {
                            if !queue.contains(&(a_child, b_child)) {
                                queue.push((a_child, b_child));
                            }
                        }
                    }
                }
                _ => return false,
            }
        }

        true
    }
}

impl<E> Default for FoldingTree<E> {
    fn default() -> Self {
        Self {
            nodes: vec![Folding::Folded],
            children: vec![IndexMap::default()],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_require(
        t: &mut FoldingTree<&'static str>,
        require: &'static [&'static str],
        expect: &[(EventKind, &[&str])],
    ) {
        eprintln!("require: {require:?}");
        let mut foldings = vec![];
        t.require(
            |kind, path| {
                eprintln!("  {kind:?} {path:?}");
                foldings.push((kind, path.to_vec()))
            },
            require.iter().copied(),
        );
        eprintln!("{t}");
        assert_eq!(
            foldings,
            expect
                .iter()
                .map(|(kind, path)| (*kind, path.to_vec()))
                .collect::<Vec<_>>()
        );
        eprintln!("\n");
    }

    #[test]
    fn basic_tree() {
        use EventKind::*;

        let mut t = FoldingTree::default();
        eprintln!("{t}");
        test_require(
            &mut t,
            &["a", "b", "c"],
            &[(Unfold, &[]), (Unfold, &["a"]), (Unfold, &["a", "b"])],
        );
        test_require(&mut t, &["a", "b", "c", "d"], &[(Unfold, &["a", "b", "c"])]);
        test_require(&mut t, &["a", "b", "c"], &[(Fold, &["a", "b", "c"])]);
        test_require(&mut t, &["a"], &[(Fold, &["a", "b"]), (Fold, &["a"])]);
    }

    #[test]
    fn basic_meet() {
        let mut a = FoldingTree::default();
        a.require(|_, _| {}, &["a", "b", "0"]);
        eprintln!("{a}");

        let mut b = FoldingTree::default();
        b.require(|_, _| {}, &["a", "b", "1"]);
        eprintln!("{b}");

        assert_eq!(a.meet(&b).to_string(), "{ a { b { } } }");
    }

    #[test]
    fn lower_meet() {
        let mut a = FoldingTree::default();
        a.require(|_, _| {}, &["a", "b", "0"]);
        eprintln!("{a}");

        let mut b = FoldingTree::default();
        b.require(|_, _| {}, &["a", "b"]);
        eprintln!("{b}");

        assert_eq!(a.meet(&b).to_string(), "{ a { b X } }");
    }

    #[test]
    fn branching_meet() {
        let mut a = FoldingTree::default();
        a.require(|_, _| {}, &["a", "b", "0"]);
        a.require(|_, _| {}, &["a", "c"]);
        eprintln!("{a}");

        let mut b = FoldingTree::default();
        b.require(|_, _| {}, &["a", "b"]);
        b.require(|_, _| {}, &["a", "c", "0"]);
        eprintln!("{b}");

        assert_eq!(a.meet(&b).to_string(), "{ a { b X c X } }");
    }

    #[test]
    fn equality() {
        let mut a = FoldingTree::default();
        a.require(|_, _| {}, &["a", "c"]);
        a.require(|_, _| {}, &["a", "b", "0"]);
        eprintln!("{a}");

        let mut b = FoldingTree::default();
        b.require(|_, _| {}, &["a", "c", "0"]);
        b.require(|_, _| {}, &["a", "b", "0"]);
        b.require(|_, _| {}, &["a", "c"]);
        eprintln!("{b}");

        assert_eq!(a, b);
    }
}
