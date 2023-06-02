use std::{
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use rowan::TextRange;

use crate::{ast::Spanned, support::AstNode, MistLanguage, SourceSpan, SyntaxNode};

pub type SyntaxNodePtr = rowan::ast::SyntaxNodePtr<MistLanguage>;

#[derive(Debug)]
pub struct AstPtr<N: AstNode> {
    raw: SyntaxNodePtr,
    _ty: PhantomData<fn() -> N>,
}

impl<N: AstNode> Clone for AstPtr<N> {
    fn clone(&self) -> AstPtr<N> {
        AstPtr { raw: self.raw.clone(), _ty: PhantomData }
    }
}

impl<N: AstNode> Eq for AstPtr<N> {}

impl<N: AstNode> PartialEq for AstPtr<N> {
    fn eq(&self, other: &AstPtr<N>) -> bool {
        self.raw == other.raw
    }
}

impl<N: AstNode> Hash for AstPtr<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

impl<N: AstNode> AstPtr<N> {
    pub fn new(node: &N) -> AstPtr<N> {
        AstPtr { raw: SyntaxNodePtr::new(node.syntax()), _ty: PhantomData }
    }

    pub fn to_node(&self, root: &SyntaxNode) -> N {
        let syntax_node = self.raw.to_node(root);
        N::cast(syntax_node).unwrap()
    }

    pub fn syntax_node_ptr(&self) -> SyntaxNodePtr {
        self.raw.clone()
    }

    pub fn text_range(&self) -> TextRange {
        self.raw.text_range()
    }

    pub fn cast<U: AstNode>(self) -> Option<AstPtr<U>> {
        if !U::can_cast(self.raw.kind()) {
            return None;
        }
        Some(AstPtr { raw: self.raw, _ty: PhantomData })
    }

    pub fn upcast<M: AstNode>(self) -> AstPtr<M>
    where
        N: Into<M>,
    {
        AstPtr { raw: self.raw, _ty: PhantomData }
    }

    /// Like `SyntaxNodePtr::cast` but the trait bounds work out.
    pub fn try_from_raw(raw: SyntaxNodePtr) -> Option<AstPtr<N>> {
        N::can_cast(raw.kind()).then_some(AstPtr { raw, _ty: PhantomData })
    }
}

impl<N: AstNode> From<AstPtr<N>> for SyntaxNodePtr {
    fn from(ptr: AstPtr<N>) -> SyntaxNodePtr {
        ptr.raw
    }
}

impl<N: AstNode> Spanned for AstPtr<N> {
    fn span(self) -> SourceSpan {
        let r = self.text_range();
        SourceSpan::new_start_end(r.start().into(), r.end().into())
    }
}

impl<N: AstNode> Spanned for &'_ AstPtr<N> {
    fn span(self) -> SourceSpan {
        let r = self.text_range();
        SourceSpan::new_start_end(r.start().into(), r.end().into())
    }
}
