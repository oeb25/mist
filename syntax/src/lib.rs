pub use generated::SourceFile;
pub(crate) use generated::SyntaxKind;
use parser::{ParseError, Parser};

mod generated;
mod parser;
mod stmt;
mod support;
#[cfg(test)]
mod tests;

pub fn parse(src: &str) -> (SourceFile, Vec<ParseError>) {
    Parser::new(src).parse()
}

#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct MintLanguage;

impl rowan::Language for MintLanguage {
    type Kind = SyntaxKind;

    fn kind_from_raw(raw: rowan::SyntaxKind) -> Self::Kind {
        SyntaxKind::from(raw.0)
    }

    fn kind_to_raw(kind: Self::Kind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind.into())
    }
}

type SyntaxToken = rowan::SyntaxToken<MintLanguage>;
type SyntaxNode = rowan::SyntaxNode<MintLanguage>;
type SyntaxNodeChildren = rowan::SyntaxNodeChildren<MintLanguage>;

// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
// #[allow(non_camel_case_types)]
// #[repr(u16)]
// pub enum SyntaxKind {
//     FN_KW,
//     LET_KW,
//     ASSUME_KW,
//     ASSERT_KW,
// }
