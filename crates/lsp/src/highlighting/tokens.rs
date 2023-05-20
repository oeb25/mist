use tower_lsp::lsp_types::{SemanticTokenModifier, SemanticTokenType};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u32)]
pub enum TokenType {
    Namespace,
    Type,
    Class,
    Enum,
    Interface,
    Struct,
    TypeParameter,
    Parameter,
    Variable,
    Property,
    EnumMember,
    Event,
    Function,
    Method,
    Macro,
    Keyword,
    Modifier,
    Comment,
    String,
    Number,
    Regexp,
    Operator,
}

impl TokenType {
    pub fn all() -> impl Iterator<Item = TokenType> {
        use self::TokenType::*;
        [
            Namespace,
            Type,
            Class,
            Enum,
            Interface,
            Struct,
            TypeParameter,
            Parameter,
            Variable,
            Property,
            EnumMember,
            Event,
            Function,
            Method,
            Macro,
            Keyword,
            Modifier,
            Comment,
            String,
            Number,
            Regexp,
            Operator,
        ]
        .into_iter()
    }
}

impl From<TokenType> for u32 {
    fn from(tt: TokenType) -> Self {
        tt as u32
    }
}
impl From<TokenType> for SemanticTokenType {
    fn from(tt: TokenType) -> Self {
        use self::TokenType::*;

        match tt {
            Namespace => SemanticTokenType::NAMESPACE,
            Type => SemanticTokenType::TYPE,
            Class => SemanticTokenType::CLASS,
            Enum => SemanticTokenType::ENUM,
            Interface => SemanticTokenType::INTERFACE,
            Struct => SemanticTokenType::STRUCT,
            TypeParameter => SemanticTokenType::TYPE_PARAMETER,
            Parameter => SemanticTokenType::PARAMETER,
            Variable => SemanticTokenType::VARIABLE,
            Property => SemanticTokenType::PROPERTY,
            EnumMember => SemanticTokenType::ENUM_MEMBER,
            Event => SemanticTokenType::EVENT,
            Function => SemanticTokenType::FUNCTION,
            Method => SemanticTokenType::METHOD,
            Macro => SemanticTokenType::MACRO,
            Keyword => SemanticTokenType::KEYWORD,
            Modifier => SemanticTokenType::MODIFIER,
            Comment => SemanticTokenType::COMMENT,
            String => SemanticTokenType::STRING,
            Number => SemanticTokenType::NUMBER,
            Regexp => SemanticTokenType::REGEXP,
            Operator => SemanticTokenType::OPERATOR,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u32)]
pub enum TokenModifier {
    Declaration,
    Definition,
    Readonly,
    Static,
    Deprecated,
    Abstract,
    Async,
    Modification,
    Documentation,
    DefaultLibrary,
}

impl TokenModifier {
    pub fn all() -> impl Iterator<Item = TokenModifier> {
        use self::TokenModifier::*;
        [
            Declaration,
            Definition,
            Readonly,
            Static,
            Deprecated,
            Abstract,
            Async,
            Modification,
            Documentation,
            DefaultLibrary,
        ]
        .into_iter()
    }
}

impl From<TokenModifier> for u32 {
    fn from(tt: TokenModifier) -> Self {
        tt as u32
    }
}
impl From<TokenModifier> for SemanticTokenModifier {
    fn from(tt: TokenModifier) -> Self {
        use self::TokenModifier::*;

        match tt {
            Declaration => SemanticTokenModifier::DECLARATION,
            Definition => SemanticTokenModifier::DEFINITION,
            Readonly => SemanticTokenModifier::READONLY,
            Static => SemanticTokenModifier::STATIC,
            Deprecated => SemanticTokenModifier::DEPRECATED,
            Abstract => SemanticTokenModifier::ABSTRACT,
            Async => SemanticTokenModifier::ASYNC,
            Modification => SemanticTokenModifier::MODIFICATION,
            Documentation => SemanticTokenModifier::DOCUMENTATION,
            DefaultLibrary => SemanticTokenModifier::DEFAULT_LIBRARY,
        }
    }
}
