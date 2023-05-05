pub(crate) use ast::SyntaxKind;
pub use parser::ParseError;
use parser::Parser;
pub use support::{AstNode, SourceSpan};

pub mod ast;
mod parser;
pub mod ptr;
mod stmt;
mod support;
#[cfg(test)]
mod tests;

pub fn parse(src: &str) -> (ast::SourceFile, Vec<ParseError>) {
    Parser::new(src).parse()
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

type SyntaxToken = rowan::SyntaxToken<MistLanguage>;
pub type SyntaxNode = rowan::SyntaxNode<MistLanguage>;
type SyntaxNodeChildren = rowan::SyntaxNodeChildren<MistLanguage>;
