use std::{marker::PhantomData, sync::Arc};

pub(crate) use ast::SyntaxKind;
pub use parser::ParseError;
use parser::Parser;
pub use rowan::{Direction, GreenNode};
pub use support::{AstNode, SourceSpan};

pub mod ast;
mod parser;
pub mod ptr;
mod stmt;
mod support;
#[cfg(test)]
mod tests;

#[derive(Debug, PartialEq, Eq)]
pub struct Parse<T> {
    green: GreenNode,
    errors: Arc<Vec<ParseError>>,
    _ty: PhantomData<fn() -> T>,
}

impl<T> Clone for Parse<T> {
    fn clone(&self) -> Self {
        Self {
            green: self.green.clone(),
            errors: self.errors.clone(),
            _ty: PhantomData,
        }
    }
}

pub fn parse(src: &str) -> Parse<ast::SourceFile> {
    let (ast, errors) = Parser::new(src).parse();
    Parse {
        green: ast.syntax().green().into_owned(),
        errors: Arc::new(errors),
        _ty: PhantomData,
    }
}

impl<T> Parse<T> {
    pub fn syntax(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.clone())
    }

    pub fn errors(&self) -> &[ParseError] {
        &self.errors
    }
}

impl<T: AstNode> Parse<T> {
    pub fn tree(&self) -> T {
        T::cast(self.syntax()).unwrap()
    }
}

#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct MistLanguage;

impl rowan::Language for MistLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        SyntaxKind::from(raw.0)
    }

    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind.into())
    }
}

pub type SyntaxToken = rowan::SyntaxToken<MistLanguage>;
pub type SyntaxNode = rowan::SyntaxNode<MistLanguage>;
pub type SyntaxNodeChildren = rowan::SyntaxNodeChildren<MistLanguage>;
pub type SyntaxElement = rowan::SyntaxElement<MistLanguage>;
