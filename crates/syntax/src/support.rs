use std::marker::PhantomData;

use crate::{SyntaxKind, SyntaxNode, SyntaxNodeChildren, SyntaxToken};

pub(super) fn child<N: AstNode>(parent: &SyntaxNode) -> Option<N> {
    parent.children().find_map(N::cast)
}

pub(super) fn children<N: AstNode>(parent: &SyntaxNode) -> AstChildren<N> {
    AstChildren::new(parent)
}

pub(super) fn token(parent: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxToken> {
    parent.children_with_tokens().filter_map(|it| it.into_token()).find(|it| it.kind() == kind)
}

/// An iterator over `SyntaxNode` children of a particular AST type.
#[derive(Debug, Clone)]
pub struct AstChildren<N> {
    inner: SyntaxNodeChildren,
    ph: PhantomData<N>,
}

impl<N> AstChildren<N> {
    fn new(parent: &SyntaxNode) -> Self {
        AstChildren { inner: parent.children(), ph: PhantomData }
    }
}

impl<N: AstNode> Iterator for AstChildren<N> {
    type Item = N;
    fn next(&mut self) -> Option<N> {
        self.inner.find_map(N::cast)
    }
}

/// The main trait to go from untyped `SyntaxNode`  to a typed ast. The
/// conversion itself has zero runtime cost: ast and syntax nodes have exactly
/// the same representation: a pointer to the tree root and a pointer to the
/// node itself.
pub trait AstNode {
    fn can_cast(kind: SyntaxKind) -> bool
    where
        Self: Sized;

    fn cast(syntax: SyntaxNode) -> Option<Self>
    where
        Self: Sized;

    fn syntax(&self) -> &SyntaxNode;
    fn clone_for_update(&self) -> Self
    where
        Self: Sized,
    {
        Self::cast(self.syntax().clone_for_update()).unwrap()
    }
    fn clone_subtree(&self) -> Self
    where
        Self: Sized,
    {
        Self::cast(self.syntax().clone_subtree()).unwrap()
    }
}

/// Like `AstNode`, but wraps tokens rather than interior nodes.
pub trait AstToken {
    fn can_cast(token: SyntaxKind) -> bool
    where
        Self: Sized;

    fn cast(syntax: SyntaxToken) -> Option<Self>
    where
        Self: Sized;

    fn syntax(&self) -> &SyntaxToken;

    fn text(&self) -> &str {
        self.syntax().text()
    }
}

impl From<u16> for SyntaxKind {
    #[inline]
    fn from(d: u16) -> SyntaxKind {
        assert!(d <= (SyntaxKind::__LAST as u16));
        unsafe { std::mem::transmute::<u16, SyntaxKind>(d) }
    }
}

impl From<SyntaxKind> for u16 {
    #[inline]
    fn from(k: SyntaxKind) -> u16 {
        k as u16
    }
}

impl From<SyntaxKind> for rowan::SyntaxKind {
    #[inline]
    fn from(k: SyntaxKind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(k as u16)
    }
}

impl SyntaxKind {
    #[inline]
    pub fn is_trivia(self) -> bool {
        matches!(self, SyntaxKind::WHITESPACE | SyntaxKind::COMMENT)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
// #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SourceSpan {
    /// The start of the span.
    offset: usize,
    /// The total length of the span. Think of this as an offset from `start`.
    length: usize,
}

impl SourceSpan {
    #[must_use]
    pub fn new_start_end(start: usize, end: usize) -> Self {
        SourceSpan { offset: start, length: end - start }
    }
    #[must_use]
    pub fn offset(&self) -> usize {
        self.offset
    }
    #[must_use]
    pub fn len(&self) -> usize {
        self.length
    }
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    #[must_use]
    pub fn set_len(&self, len: usize) -> Self {
        Self { offset: self.offset, length: len }
    }
    #[must_use]
    pub fn join(&self, span: SourceSpan) -> SourceSpan {
        let offset = self.offset.min(span.offset);
        let end = self.end().max(span.end());
        let length = end - offset;
        SourceSpan { offset, length }
    }
    #[must_use]
    pub fn end(&self) -> usize {
        self.offset + self.length
    }
    #[must_use]
    pub fn contains(&self, byte_offset: usize) -> bool {
        self.offset() <= byte_offset && byte_offset <= self.end()
    }

    #[must_use]
    pub fn union(
        init: SourceSpan,
        span: impl IntoIterator<Item = Option<SourceSpan>>,
    ) -> SourceSpan {
        span.into_iter().fold(init, |a, b| b.map(|b| a.join(b)).unwrap_or(a))
    }

    #[must_use]
    pub fn overlaps(&self, other: SourceSpan) -> bool {
        self.contains(other.offset())
            || self.contains(other.end())
            || other.contains(self.offset())
            || other.contains(self.end())
    }
}

impl From<SourceSpan> for miette::SourceSpan {
    fn from(s: SourceSpan) -> Self {
        Self::new(s.offset.into(), s.length.into())
    }
}
impl From<(usize, usize)> for SourceSpan {
    fn from((offset, length): (usize, usize)) -> Self {
        SourceSpan { offset, length }
    }
}
