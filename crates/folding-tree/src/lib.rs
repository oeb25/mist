use std::{fmt, hash::Hash, iter};

use indexmap::{map::Entry, IndexMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Folding {
    Uninitialized,
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

#[derive(Debug, Clone)]
pub struct FoldingTree<E> {
    nodes: Vec<Folding>,
    children: Vec<IndexMap<E, usize>>,
}

impl<E: fmt::Display> fmt::Display for FoldingTree<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut in_block = false;
        let mut prefix_space = false;
        for event in self.preorder() {
            if in_block && prefix_space {
                write!(f, " ")?;
            }
            match event {
                WalkEvent::Enter((edge, folding)) => {
                    prefix_space = true;
                    if let Some(edge) = edge {
                        write!(f, "{edge} ")?;
                    }

                    match folding {
                        Folding::Uninitialized => write!(f, "@")?,
                        Folding::Folded => write!(f, "X")?,
                        Folding::Unfolded => {
                            write!(f, "{{")?;
                            in_block = true;
                        }
                    }
                }
                WalkEvent::Leave((_, folding)) => {
                    if let Folding::Unfolded = folding {
                        write!(f, "}}")?;
                        prefix_space = true;
                    } else {
                        prefix_space = false;
                    }
                }
            }
        }
        Ok(())
    }
}

impl<'a> TryFrom<&'a str> for FoldingTree<&'a str> {
    type Error = std::fmt::Error;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        #[derive(Debug)]
        enum Token<'a> {
            LBra,
            RBra,
            Word(&'a str),
        }

        struct Tokenizer<'a> {
            src: &'a str,
            chars: std::str::CharIndices<'a>,
        }

        impl<'a> Tokenizer<'a> {
            fn new(src: &str) -> Tokenizer {
                Tokenizer { src, chars: src.char_indices() }
            }
        }

        impl<'a> Iterator for Tokenizer<'a> {
            type Item = Token<'a>;

            fn next(&mut self) -> Option<Self::Item> {
                let mut start = None;
                for (idx, c) in &mut self.chars {
                    match c {
                        c if c.is_whitespace() => {
                            if let Some(start) = start {
                                return Some(Token::Word(&self.src[start..idx]));
                            }
                        }
                        '{' => return Some(Token::LBra),
                        '}' => return Some(Token::RBra),
                        _ => {
                            if start.is_none() {
                                start = Some(idx)
                            }
                        }
                    }
                }
                if let Some(start) = start {
                    return Some(Token::Word(&self.src[start..self.src.len()]));
                }
                None
            }
        }

        let mut tokens = Tokenizer::new(s);

        fn parse_block<'a>(
            prefix: &[&'a str],
            t: &mut Tokenizer<'a>,
            ft: &mut FoldingTree<&'a str>,
        ) -> Option<Folding> {
            match t.next()? {
                Token::LBra => {
                    ft.require(|_, _| {}, prefix.iter().copied());
                    loop {
                        match t.next()? {
                            Token::LBra => todo!("unexpected nesting"),
                            Token::RBra => break,
                            Token::Word(f) => {
                                let mut prefix = prefix.to_vec();
                                prefix.push(f);
                                let _ = parse_block(&prefix, t, ft)?;
                            }
                        }
                    }
                    Some(Folding::Unfolded)
                }
                Token::RBra => todo!(),
                Token::Word("X") => {
                    ft.require(|_, _| {}, prefix.iter().copied());
                    Some(Folding::Folded)
                }
                Token::Word(w) => todo!("word: {w:?}"),
            }
        }

        let mut ft = FoldingTree::folded();

        parse_block(&[], &mut tokens, &mut ft);

        Ok(ft)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EventKind {
    Unfold,
    Fold,
}

impl<E> FoldingTree<E> {
    pub fn folded() -> FoldingTree<E> {
        FoldingTree { nodes: vec![Folding::Folded], children: vec![IndexMap::default()] }
    }

    pub fn require(
        &mut self,
        mut events: impl for<'a> FnMut(EventKind, &'a [E]),
        path: impl IntoIterator<Item = E>,
    ) where
        E: PartialEq + Eq + Hash + Clone,
    {
        use Folding::*;

        let mut current_node = 0;
        let mut current_path = Vec::new();

        for edge in path {
            let next_idx = self.next_idx();
            let children = &mut self.children[current_node];
            let was = self.nodes[current_node];
            if self.nodes[current_node].is_folded() {
                events(EventKind::Unfold, &current_path);
            }

            let next_node = match children.entry(edge.clone()) {
                Entry::Occupied(it) => *it.get(),
                Entry::Vacant(it) => {
                    it.insert(next_idx);
                    if was.is_folded() {
                        self.alloc_folded()
                    } else {
                        self.alloc_uninitialized()
                    }
                }
            };

            if !self.nodes[current_node].is_unfolded() {
                self.unfold_node(current_node);
            }
            current_node = next_node;

            current_path.push(edge);
        }

        if self.nodes[current_node].is_folded() {
            return;
        }

        let mut folding_stack = vec![(current_node, current_path.len(), None)];

        while let Some((idx, n, edge)) = folding_stack.pop() {
            current_path.truncate(n);
            if let Some(edge) = edge.clone() {
                current_path.push(edge);
            }
            if self.nodes[idx].is_folded() {
                continue;
            }
            if self.children[idx].iter().all(|(_, &child_idx)| self.nodes[child_idx].is_folded()) {
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

    pub fn fold(&mut self, path: impl IntoIterator<Item = E>) -> Result<(), FoldError>
    where
        E: PartialEq + Eq + Hash + Clone,
    {
        let mut current_idx = 0;

        for e in path {
            match self.nodes[current_idx] {
                Folding::Uninitialized => return Err(FoldError::WasUninitialized),
                Folding::Folded => return Err(FoldError::AlreadyFolded),
                Folding::Unfolded => {
                    if let Some(next_idx) = self.children[current_idx].get(&e) {
                        current_idx = *next_idx;
                    } else {
                        return Err(FoldError::Inaccessible);
                    }
                }
            }
        }

        self.nodes[current_idx] = Folding::Folded;

        Ok(())
    }

    pub fn unfold(&mut self, path: impl IntoIterator<Item = E>) -> Result<(), UnfoldError>
    where
        E: PartialEq + Eq + Hash + Clone,
    {
        let mut current_idx = 0;

        for e in path {
            match self.nodes[current_idx] {
                Folding::Uninitialized => return Err(UnfoldError::WasUninitialized),
                Folding::Folded => return Err(UnfoldError::Inaccessible),
                Folding::Unfolded => {
                    if let Some(next_idx) = self.children[current_idx].get(&e) {
                        current_idx = *next_idx;
                    } else {
                        return Err(UnfoldError::Inaccessible);
                    }
                }
            }
        }

        self.unfold_node(current_idx);

        Ok(())
    }

    fn unfold_node(&mut self, idx: usize)
    where
        E: PartialEq + Eq + Hash + Clone,
    {
        self.nodes[idx] = Folding::Unfolded;
        for (_, child_idx) in &self.children[idx] {
            self.nodes[*child_idx] = Folding::Folded;
        }
    }

    pub fn drop(&mut self, path: impl IntoIterator<Item = E>)
    where
        E: PartialEq + Eq + Hash + Clone + fmt::Debug,
    {
        let mut current_idx = 0;

        for e in path {
            match self.nodes[current_idx] {
                Folding::Uninitialized => return,
                Folding::Folded => return,
                Folding::Unfolded => {
                    if let Some(next_idx) = self.children[current_idx].get(&e) {
                        current_idx = *next_idx;
                    } else {
                        return;
                    }
                }
            }
        }

        self.nodes[current_idx] = Folding::Uninitialized;
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
            m.nodes[m_idx] = match (
                (self.nodes[a_idx], &self.children[a_idx]),
                (other.nodes[b_idx], &other.children[b_idx]),
            ) {
                ((Uninitialized, _), (Uninitialized, _)) => Uninitialized,
                ((Uninitialized, _), (b_fold, b_children)) => {
                    queue.extend(b_children.iter().map(|(edge, &b_child)| {
                        let m_child = m.alloc_uninitialized();
                        m.children[m_idx].insert(edge.clone(), m_child);
                        (m_child, a_idx, b_child)
                    }));
                    b_fold
                }
                ((a_fold, a_children), (Uninitialized, _)) => {
                    queue.extend(a_children.iter().map(|(edge, &a_child)| {
                        let m_child = m.alloc_uninitialized();
                        m.children[m_idx].insert(edge.clone(), m_child);
                        (m_child, a_child, b_idx)
                    }));
                    a_fold
                }
                ((Unfolded, a_children), (Unfolded, b_children)) => {
                    let a = a_children.iter().filter_map(|(edge, &a_child)| {
                        Some((edge, a_child, *b_children.get(edge)?))
                    });
                    let b = b_children.iter().filter_map(|(edge, &b_child)| {
                        Some((edge, *a_children.get(edge)?, b_child))
                    });

                    queue.extend(a.chain(b).filter_map(|(edge, a_child, b_child)| {
                        if m.children[m_idx].contains_key(edge) {
                            return None;
                        }
                        let m_child = m.alloc_uninitialized();
                        m.children[m_idx].insert(edge.clone(), m_child);
                        Some((m_child, a_child, b_child))
                    }));

                    Unfolded
                }
                _ => Folded,
            };
        }

        m
    }

    #[must_use]
    pub fn contains(&self, other: &FoldingTree<E>) -> bool
    where
        E: PartialEq + Eq + Hash,
    {
        use Folding::*;

        let a = self;
        let b = other;

        let mut queue = vec![(0, 0)];

        while let Some((a_idx, b_idx)) = queue.pop() {
            match (a.nodes[a_idx], b.nodes[b_idx]) {
                (_, Uninitialized) | (Folded, _) => {}
                (Unfolded, Unfolded) => {
                    let a_iter = a.children[a_idx].iter().filter_map(|(edge, &a_child)| {
                        Some((a_child, *b.children[b_idx].get(edge)?))
                    });
                    let b_iter = b.children[b_idx].iter().filter_map(|(edge, &b_child)| {
                        Some((*a.children[a_idx].get(edge)?, b_child))
                    });

                    for it in a_iter.chain(b_iter) {
                        if !queue.contains(&(it)) {
                            queue.push(it);
                        }
                    }
                }
                _ => return false,
            }
        }

        true
    }

    pub fn folded_iter(&self) -> impl Iterator<Item = Vec<&E>> {
        let mut current_path = vec![];
        let mut queue = vec![(0, 0, None)];

        iter::from_fn(move || {
            while let Some((idx, n, edge)) = queue.pop() {
                current_path.truncate(n);
                if let Some(edge) = edge {
                    current_path.push(edge);
                }

                if self.nodes[idx].is_unfolded() {
                    for (edge, &child) in &self.children[idx] {
                        queue.push((child, current_path.len(), Some(edge.clone())));
                    }
                } else if self.nodes[idx].is_folded() {
                    return Some(current_path.to_vec());
                }
            }

            None
        })
    }

    pub fn transition_into(
        &mut self,
        mut events: impl for<'a> FnMut(EventKind, &'a [E]),
        target: &FoldingTree<E>,
    ) where
        E: PartialEq + Eq + Hash + Clone,
    {
        for path in target.folded_iter() {
            self.require(&mut events, path.into_iter().cloned())
        }
    }

    pub fn map_edges<T>(&self, mut f: impl FnMut(&E) -> T) -> FoldingTree<T>
    where
        E: PartialEq + Eq + Hash + Clone,
        T: PartialEq + Eq + Hash,
    {
        FoldingTree {
            nodes: self.nodes.clone(),
            children: self
                .children
                .iter()
                .map(|children| children.iter().map(|(e, idx)| (f(e), *idx)).collect())
                .collect(),
        }
    }

    pub fn is_folded(&self) -> bool {
        self.nodes[0].is_folded()
    }

    pub fn preorder(&self) -> impl Iterator<Item = WalkEvent<(Option<&E>, Folding)>> {
        let mut stack = vec![WalkEvent::Enter((None, 0))];

        iter::from_fn(move || {
            let event = stack.pop()?;

            if let WalkEvent::Enter((edge, idx)) = event {
                stack.push(WalkEvent::Leave((edge, idx)));
                if let Folding::Unfolded = self.nodes[idx] {
                    for (edge, child) in self.children[idx].iter().rev() {
                        stack.push(WalkEvent::Enter((Some(edge), *child)))
                    }
                }
            }

            Some(event.map(|(edge, idx)| (*edge, self.nodes[*idx])))
        })
    }
}

pub enum FoldError {
    Inaccessible,
    AlreadyFolded,
    WasUninitialized,
}
pub enum UnfoldError {
    Inaccessible,
    AlreadyUnfolded,
    WasUninitialized,
}

#[derive(Debug, Clone)]
pub enum WalkEvent<T> {
    Enter(T),
    Leave(T),
}

impl<T> WalkEvent<T> {
    pub fn map<S>(&self, f: impl Fn(&T) -> S) -> WalkEvent<S> {
        match self {
            WalkEvent::Enter(e) => WalkEvent::Enter(f(e)),
            WalkEvent::Leave(e) => WalkEvent::Leave(f(e)),
        }
    }
}

impl<E> FoldingTree<E> {
    fn next_idx(&self) -> usize {
        self.nodes.len()
    }
    fn alloc_uninitialized(&mut self) -> usize {
        let idx = self.nodes.len();
        self.nodes.push(Folding::Uninitialized);
        self.children.push(IndexMap::default());
        idx
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
                (Folded, Folded) | (Uninitialized, Uninitialized) => {}
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

impl<E> Eq for FoldingTree<E> where E: PartialEq + Eq + Hash {}

impl<E> Default for FoldingTree<E> {
    fn default() -> Self {
        Self { nodes: vec![Folding::Uninitialized], children: vec![IndexMap::default()] }
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
            expect.iter().map(|(kind, path)| (*kind, path.to_vec())).collect::<Vec<_>>()
        );
        eprintln!("\n");
    }

    #[test]
    fn basic_tree() {
        use EventKind::*;

        let mut t = FoldingTree::folded();
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
        let mut a = FoldingTree::folded();
        a.require(|_, _| {}, &["a", "b", "0"]);
        eprintln!("{a}");

        let mut b = FoldingTree::folded();
        b.require(|_, _| {}, &["a", "b", "1"]);
        eprintln!("{b}");

        assert_eq!(a.meet(&b).to_string(), "{ a { b { } } }");
    }

    #[test]
    fn another_meet() {
        let mut a = FoldingTree::folded();
        a.require(|_, _| {}, &["a"]);
        eprintln!("{a}");

        let b = FoldingTree::folded();
        eprintln!("{b}");

        assert_eq!(a.meet(&b).to_string(), "X");
        assert_eq!(b.meet(&a).to_string(), "X");
    }

    #[test]
    fn idempotent_meet() {
        let mut a = FoldingTree::default();
        a.require(|_, _| {}, &["a"]);
        eprintln!("{a}");

        assert_eq!(a.meet(&a).to_string(), "{ a X }");
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

    #[test]
    fn identity() {
        let mut a = FoldingTree::default();
        a.require(|_, _| {}, &["a", "c"]);
        a.require(|_, _| {}, &["a", "b", "0"]);
        eprintln!("{a}");
        let t = a.meet(&FoldingTree::default());
        assert_eq!(t, a, "{t}");
        let t = FoldingTree::default().meet(&a);
        assert_eq!(t, a, "{t}");

        let mut b = FoldingTree::default();
        b.require(|_, _| {}, &["a", "c", "0"]);
        b.require(|_, _| {}, &["a", "b", "0"]);
        eprintln!("{b}");
        let t = b.meet(&FoldingTree::default());
        assert_eq!(t, b, "{t}");
        let t = FoldingTree::default().meet(&b);
        assert_eq!(t, b, "{t}");
    }

    #[test]
    fn drop() {
        let mut a = FoldingTree::default();
        a.require(|_, _| {}, &["a", "b"]);
        eprintln!("{a}");
        a.drop(&["a"]);
        eprintln!("{a}");
    }

    #[test]
    fn parse() {
        let s = "{ a { f X } b X }";
        let t = FoldingTree::try_from(s).unwrap();
        assert_eq!(t.to_string(), s);
    }
}
