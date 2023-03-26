mod expr_ext;
mod generated;
pub mod operators;

pub use expr_ext::LiteralKind;
pub use generated::*;

use crate::{support::AstNode, SourceSpan, SyntaxNode, SyntaxToken};

pub struct Pure<T>(T);

impl<T> PartialEq for Pure<T>
where
    T: AstNode,
{
    fn eq(&self, other: &Self) -> bool {
        self.0.syntax().text() == other.0.syntax().text()
    }
}

impl<T> From<T> for Pure<T>
where
    T: AstNode,
{
    fn from(value: T) -> Self {
        Pure(value)
    }
}

pub trait Spanned {
    fn span(&self) -> SourceSpan;
}

impl<T> Spanned for T
where
    T: AstNode,
{
    fn span(&self) -> SourceSpan {
        self.syntax().span()
    }
}
impl Spanned for SyntaxNode {
    fn span(&self) -> SourceSpan {
        let range = self.text_range();
        SourceSpan::new_start_end(range.start().into(), range.end().into())
    }
}
impl Spanned for SyntaxToken {
    fn span(&self) -> SourceSpan {
        let range = self.text_range();
        SourceSpan::new_start_end(range.start().into(), range.end().into())
    }
}

impl PartialEq<std::string::String> for Name {
    fn eq(&self, other: &std::string::String) -> bool {
        self.ident_token().unwrap().text() == other
    }
}
impl PartialEq<Name> for std::string::String {
    fn eq(&self, other: &Name) -> bool {
        if let Some(n) = other.ident_token() {
            n.text() == self
        } else {
            false
        }
    }
}
impl PartialEq<&'_ str> for Name {
    fn eq(&self, other: &&str) -> bool {
        self.ident_token().unwrap().text() == *other
    }
}
