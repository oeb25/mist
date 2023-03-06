pub(crate) use ast::SyntaxKind;
pub use parser::ParseError;
use parser::Parser;
pub use support::SourceSpan;

pub mod ast;
mod parser;
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
type SyntaxNode = rowan::SyntaxNode<MistLanguage>;
type SyntaxNodeChildren = rowan::SyntaxNodeChildren<MistLanguage>;

// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
// #[allow(non_camel_case_types)]
// #[repr(u16)]
// pub enum SyntaxKind {
//     FN_KW,
//     LET_KW,
//     ASSUME_KW,
//     ASSERT_KW,
// }
