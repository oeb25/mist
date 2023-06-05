mod expr_ext;
mod generated;
mod items_ext;
mod node_ext;
pub mod operators;
mod traits;

pub use expr_ext::LiteralKind;
pub use generated::*;
pub use items_ext::AttrFlags;
pub use node_ext::NameOrNameRef;
pub use traits::{HasAttrs, HasExpr, HasName};

use crate::{support::AstNode, SourceSpan, SyntaxElement, SyntaxNode, SyntaxToken};

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
    fn span(self) -> SourceSpan;
    fn contains_pos(self, byte_offset: usize) -> bool
    where
        Self: Copy,
    {
        self.span().contains(byte_offset)
    }
}

// impl<T> Spanned for T
// where
//     T: AstNode,
// {
//     fn span(&self) -> SourceSpan {
//         self.syntax().span()
//     }
// }
impl<T> Spanned for &'_ T
where
    T: AstNode,
{
    fn span(self) -> SourceSpan {
        self.syntax().span()
    }
}
impl Spanned for SourceSpan {
    fn span(self) -> SourceSpan {
        self
    }
}
impl Spanned for &'_ SourceSpan {
    fn span(self) -> SourceSpan {
        *self
    }
}
impl Spanned for &'_ SyntaxNode {
    fn span(self) -> SourceSpan {
        let range = self.text_range();
        SourceSpan::new_start_end(range.start().into(), range.end().into())
    }
}
impl Spanned for SyntaxToken {
    fn span(self) -> SourceSpan {
        let range = self.text_range();
        SourceSpan::new_start_end(range.start().into(), range.end().into())
    }
}
impl Spanned for SyntaxElement {
    fn span(self) -> SourceSpan {
        let range = self.text_range();
        SourceSpan::new_start_end(range.start().into(), range.end().into())
    }
}
macro_rules! tuple_span {
    ($($t:ident: $n:tt),*; $e:ident: $m:tt) => {
        impl<$($t: Spanned,)* $e: Spanned> Spanned for ($(Option<$t>,)* $e) {
            fn span(self) -> SourceSpan {
                None
                    $(.or_else(|| (self.$n).map(|a| a.span())))*
                    .unwrap_or_else(|| self.$m.span())
            }
        }
    };
}
tuple_span!(A: 0; X: 1);
tuple_span!(A: 0, B: 1; X: 2);
tuple_span!(A: 0, B: 1, C: 2; X: 3);
tuple_span!(A: 0, B: 1, C: 2, D: 3; X: 4);

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
        if let Some(ident) = self.ident_token() {
            ident.text() == *other
        } else {
            other.is_empty()
        }
    }
}
