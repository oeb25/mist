#![allow(bad_style, missing_docs, unreachable_pub, dead_code, unused)]
use crate::{support, SyntaxNode, SyntaxNodeChildren, SyntaxToken};
use support::{AstChildren, AstNode, AstToken};

#[doc = r" The kind of syntax node, e.g. `IDENT`, `USE_KW`, or `STRUCT`."]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, logos :: Logos)]
#[repr(u16)]
pub enum SyntaxKind {
    #[doc(hidden)]
    TOMBSTONE,
    #[doc(hidden)]
    EOF,
    #[doc = r" Punctuation"]
    #[token(";")]
    SEMICOLON,
    #[token(",")]
    COMMA,
    #[token("(")]
    L_PAREN,
    #[token(")")]
    R_PAREN,
    #[token("{")]
    L_CURLY,
    #[token("}")]
    R_CURLY,
    #[token("[")]
    L_BRACK,
    #[token("]")]
    R_BRACK,
    #[token("<")]
    L_ANGLE,
    #[token(">")]
    R_ANGLE,
    #[token("@")]
    AT,
    #[token("#")]
    POUND,
    #[token("~")]
    TILDE,
    #[token("?")]
    QUESTION,
    #[token("$")]
    DOLLAR,
    #[token("&")]
    AMP,
    #[token("|")]
    PIPE,
    #[token("+")]
    PLUS,
    #[token("*")]
    STAR,
    #[token("/")]
    SLASH,
    #[token("^")]
    CARET,
    #[token("%")]
    PERCENT,
    #[token("_")]
    UNDERSCORE,
    #[token(".")]
    DOT,
    #[token("..")]
    DOT2,
    #[token("...")]
    DOT3,
    #[token("..=")]
    DOT2EQ,
    #[token(":")]
    COLON,
    #[token("::")]
    COLON2,
    #[token("=")]
    EQ,
    #[token("==")]
    EQ2,
    #[token("=>")]
    FAT_ARROW,
    #[token("!")]
    BANG,
    #[token("!=")]
    NEQ,
    #[token("-")]
    MINUS,
    #[token("->")]
    THIN_ARROW,
    #[token("<=")]
    LTEQ,
    #[token(">=")]
    GTEQ,
    #[token("+=")]
    PLUSEQ,
    #[token("-=")]
    MINUSEQ,
    #[token("|=")]
    PIPEEQ,
    #[token("&=")]
    AMPEQ,
    #[token("^=")]
    CARETEQ,
    #[token("/=")]
    SLASHEQ,
    #[token("*=")]
    STAREQ,
    #[token("%=")]
    PERCENTEQ,
    #[token("&&")]
    AMP2,
    #[token("||")]
    PIPE2,
    #[token("<<")]
    SHL,
    #[token(">>")]
    SHR,
    #[token("<<=")]
    SHLEQ,
    #[token(">>=")]
    SHREQ,
    #[doc = r" Keywords"]
    #[token("as")]
    AS_KW,
    #[token("async")]
    ASYNC_KW,
    #[token("await")]
    AWAIT_KW,
    #[token("assert")]
    ASSERT_KW,
    #[token("assume")]
    ASSUME_KW,
    #[token("box")]
    BOX_KW,
    #[token("break")]
    BREAK_KW,
    #[token("const")]
    CONST_KW,
    #[token("continue")]
    CONTINUE_KW,
    #[token("crate")]
    CRATE_KW,
    #[token("do")]
    DO_KW,
    #[token("dyn")]
    DYN_KW,
    #[token("else")]
    ELSE_KW,
    #[token("enum")]
    ENUM_KW,
    #[token("extern")]
    EXTERN_KW,
    #[token("false")]
    FALSE_KW,
    #[token("fn")]
    FN_KW,
    #[token("for")]
    FOR_KW,
    #[token("if")]
    IF_KW,
    #[token("impl")]
    IMPL_KW,
    #[token("in")]
    IN_KW,
    #[token("let")]
    LET_KW,
    #[token("loop")]
    LOOP_KW,
    #[token("macro")]
    MACRO_KW,
    #[token("match")]
    MATCH_KW,
    #[token("mod")]
    MOD_KW,
    #[token("move")]
    MOVE_KW,
    #[token("mut")]
    MUT_KW,
    #[token("pub")]
    PUB_KW,
    #[token("ref")]
    REF_KW,
    #[token("return")]
    RETURN_KW,
    #[token("self")]
    SELF_KW,
    #[token("Self")]
    SELF_TYPE_KW,
    #[token("static")]
    STATIC_KW,
    #[token("struct")]
    STRUCT_KW,
    #[token("super")]
    SUPER_KW,
    #[token("trait")]
    TRAIT_KW,
    #[token("true")]
    TRUE_KW,
    #[token("try")]
    TRY_KW,
    #[token("type")]
    TYPE_KW,
    #[token("unsafe")]
    UNSAFE_KW,
    #[token("use")]
    USE_KW,
    #[token("where")]
    WHERE_KW,
    #[token("while")]
    WHILE_KW,
    #[token("yield")]
    YIELD_KW,
    #[token("int")]
    INT_KW,
    #[token("bool")]
    BOOL_KW,
    #[token("null")]
    NULL_KW,
    #[token("result")]
    RESULT_KW,
    #[token("ghost")]
    GHOST_KW,
    #[token("pure")]
    PURE_KW,
    #[token("requires")]
    REQUIRES_KW,
    #[token("ensures")]
    ENSURES_KW,
    #[token("decreases")]
    DECREASES_KW,
    #[token("invariant")]
    INVARIANT_KW,
    #[token("req")]
    REQ_KW,
    #[token("ens")]
    ENS_KW,
    #[token("dec")]
    DEC_KW,
    #[token("inv")]
    INV_KW,
    #[token("forall")]
    FORALL_KW,
    #[token("exists")]
    EXISTS_KW,
    #[token("auto")]
    AUTO_KW,
    #[token("default")]
    DEFAULT_KW,
    #[token("existential")]
    EXISTENTIAL_KW,
    #[token("raw")]
    RAW_KW,
    #[token("macro_rules")]
    MACRO_RULES_KW,
    #[token("yeet")]
    YEET_KW,
    #[doc = r" Literals"]
    #[regex(r"0|[1-9][0-9]*")]
    INT_NUMBER,
    FLOAT_NUMBER,
    CHAR,
    BYTE,
    STRING,
    BYTE_STRING,
    #[doc = r" Tokens"]
    ERROR,
    #[regex(r"[a-zA-Z_][a-zA-Z_0-9]*")]
    IDENT,
    #[regex(r"[ \t\n\f]+")]
    WHITESPACE,
    LIFETIME_IDENT,
    #[regex(r"//.*\n")]
    COMMENT,
    SHEBANG,
    #[doc = r" Nodes"]
    SOURCE_FILE,
    STRUCT,
    ENUM,
    FN,
    MACRO,
    TYPE_INVARIANT,
    RET_TYPE,
    EXTERN_CRATE,
    MODULE,
    USE,
    STATIC,
    CONST,
    TRAIT,
    IMPL,
    TYPE_ALIAS,
    MACRO_CALL,
    MACRO_RULES,
    MACRO_ARM,
    TOKEN_TREE,
    MACRO_DEF,
    NAMED_TYPE,
    PAREN_TYPE,
    TUPLE_TYPE,
    MACRO_TYPE,
    NEVER_TYPE,
    PATH_TYPE,
    PTR_TYPE,
    ARRAY_TYPE,
    SLICE_TYPE,
    LIST_TYPE,
    REF_TYPE,
    GHOST_TYPE,
    INFER_TYPE,
    FN_PTR_TYPE,
    FOR_TYPE,
    IMPL_TRAIT_TYPE,
    DYN_TRAIT_TYPE,
    OR_PAT,
    PAREN_PAT,
    REF_PAT,
    BOX_PAT,
    IDENT_PAT,
    WILDCARD_PAT,
    REST_PAT,
    PATH_PAT,
    RECORD_PAT,
    RECORD_PAT_FIELD_LIST,
    RECORD_PAT_FIELD,
    TUPLE_STRUCT_PAT,
    TUPLE_PAT,
    SLICE_PAT,
    RANGE_PAT,
    LITERAL_PAT,
    MACRO_PAT,
    CONST_BLOCK_PAT,
    TUPLE_EXPR,
    ARRAY_EXPR,
    LIST_EXPR,
    PAREN_EXPR,
    PATH_EXPR,
    IDENT_EXPR,
    NULL_EXPR,
    RESULT_EXPR,
    CLOSURE_EXPR,
    QUANTIFIER_EXPR,
    QUANTIFIER_OVER,
    QUANTIFIER,
    NAME_IN_EXPR,
    IF_EXPR,
    WHILE_EXPR,
    LOOP_EXPR,
    FOR_EXPR,
    CONTINUE_EXPR,
    BREAK_EXPR,
    LABEL,
    BLOCK_EXPR,
    STMT_LIST,
    RETURN_EXPR,
    WHILE_STMT,
    YIELD_EXPR,
    YEET_EXPR,
    LET_EXPR,
    UNDERSCORE_EXPR,
    MACRO_EXPR,
    MATCH_EXPR,
    MATCH_ARM_LIST,
    MATCH_ARM,
    MATCH_GUARD,
    RECORD_EXPR,
    RECORD_EXPR_FIELD_LIST,
    RECORD_EXPR_FIELD,
    STRUCT_EXPR_FIELD,
    COMMA_EXPR,
    BOX_EXPR,
    CALL_EXPR,
    STRUCT_EXPR,
    INDEX_EXPR,
    NOT_NULL_EXPR,
    METHOD_CALL_EXPR,
    FIELD_EXPR,
    AWAIT_EXPR,
    TRY_EXPR,
    CAST_EXPR,
    REF_EXPR,
    PREFIX_EXPR,
    RANGE_EXPR,
    BIN_EXPR,
    EXTERN_BLOCK,
    EXTERN_ITEM_LIST,
    VARIANT,
    RECORD_FIELD_LIST,
    RECORD_FIELD,
    STRUCT_FIELD,
    TUPLE_FIELD_LIST,
    TUPLE_FIELD,
    VARIANT_LIST,
    ITEM_LIST,
    ASSOC_ITEM_LIST,
    ATTR,
    ATTRS,
    META,
    FN_ATTR,
    USE_TREE,
    USE_TREE_LIST,
    PATH,
    PATH_SEGMENT,
    LITERAL,
    RENAME,
    VISIBILITY,
    WHERE_CLAUSE,
    WHERE_PRED,
    CONDITION,
    REQUIRES,
    ENSURES,
    DECREASES,
    INVARIANT,
    ABI,
    NAME,
    NAME_REF,
    PRIMITIVE,
    OPTIONAL,
    ASSUME_STMT,
    ASSERT_STMT,
    LET_STMT,
    LET_ELSE,
    EXPR_STMT,
    GENERIC_PARAM_LIST,
    GENERIC_PARAM,
    LIFETIME_PARAM,
    TYPE_PARAM,
    CONST_PARAM,
    GENERIC_ARG_LIST,
    GENERIC_ARG,
    LIFETIME,
    LIFETIME_ARG,
    TYPE_ARG,
    ASSOC_TYPE_ARG,
    CONST_ARG,
    PARAM_LIST,
    PARAM,
    SELF_PARAM,
    ARG_LIST,
    ARG,
    TYPE_BOUND,
    TYPE_BOUND_LIST,
    MACRO_ITEMS,
    MACRO_STMTS,
    #[doc(hidden)]
    __LAST,
}
use self::SyntaxKind::*;
impl std::fmt::Display for SyntaxKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            SEMICOLON => ";",
            COMMA => ",",
            L_PAREN => "(",
            R_PAREN => ")",
            L_CURLY => "{",
            R_CURLY => "}",
            L_BRACK => "[",
            R_BRACK => "]",
            L_ANGLE => "<",
            R_ANGLE => ">",
            AT => "@",
            POUND => "#",
            TILDE => "~",
            QUESTION => "?",
            DOLLAR => "$",
            AMP => "&",
            PIPE => "|",
            PLUS => "+",
            STAR => "*",
            SLASH => "/",
            CARET => "^",
            PERCENT => "%",
            UNDERSCORE => "_",
            DOT => ".",
            DOT2 => "..",
            DOT3 => "...",
            DOT2EQ => "..=",
            COLON => ":",
            COLON2 => "::",
            EQ => "=",
            EQ2 => "==",
            FAT_ARROW => "=>",
            BANG => "!",
            NEQ => "!=",
            MINUS => "-",
            THIN_ARROW => "->",
            LTEQ => "<=",
            GTEQ => ">=",
            PLUSEQ => "+=",
            MINUSEQ => "-=",
            PIPEEQ => "|=",
            AMPEQ => "&=",
            CARETEQ => "^=",
            SLASHEQ => "/=",
            STAREQ => "*=",
            PERCENTEQ => "%=",
            AMP2 => "&&",
            PIPE2 => "||",
            SHL => "<<",
            SHR => ">>",
            SHLEQ => "<<=",
            SHREQ => ">>=",
            _ => return write!(f, "{self:?}"),
        };
        write!(f, "{s}")
    }
}
impl SyntaxKind {
    pub fn is_keyword(self) -> bool {
        matches!(
            self,
            AS_KW
                | ASYNC_KW
                | AWAIT_KW
                | ASSERT_KW
                | ASSUME_KW
                | BOX_KW
                | BREAK_KW
                | CONST_KW
                | CONTINUE_KW
                | CRATE_KW
                | DO_KW
                | DYN_KW
                | ELSE_KW
                | ENUM_KW
                | EXTERN_KW
                | FALSE_KW
                | FN_KW
                | FOR_KW
                | IF_KW
                | IMPL_KW
                | IN_KW
                | LET_KW
                | LOOP_KW
                | MACRO_KW
                | MATCH_KW
                | MOD_KW
                | MOVE_KW
                | MUT_KW
                | PUB_KW
                | REF_KW
                | RETURN_KW
                | SELF_KW
                | SELF_TYPE_KW
                | STATIC_KW
                | STRUCT_KW
                | SUPER_KW
                | TRAIT_KW
                | TRUE_KW
                | TRY_KW
                | TYPE_KW
                | UNSAFE_KW
                | USE_KW
                | WHERE_KW
                | WHILE_KW
                | YIELD_KW
                | INT_KW
                | BOOL_KW
                | NULL_KW
                | RESULT_KW
                | GHOST_KW
                | PURE_KW
                | REQUIRES_KW
                | ENSURES_KW
                | DECREASES_KW
                | INVARIANT_KW
                | REQ_KW
                | ENS_KW
                | DEC_KW
                | INV_KW
                | FORALL_KW
                | EXISTS_KW
                | AUTO_KW
                | DEFAULT_KW
                | EXISTENTIAL_KW
                | RAW_KW
                | MACRO_RULES_KW
                | YEET_KW
        )
    }
    pub fn is_punct(self) -> bool {
        matches!(
            self,
            SEMICOLON
                | COMMA
                | L_PAREN
                | R_PAREN
                | L_CURLY
                | R_CURLY
                | L_BRACK
                | R_BRACK
                | L_ANGLE
                | R_ANGLE
                | AT
                | POUND
                | TILDE
                | QUESTION
                | DOLLAR
                | AMP
                | PIPE
                | PLUS
                | STAR
                | SLASH
                | CARET
                | PERCENT
                | UNDERSCORE
                | DOT
                | DOT2
                | DOT3
                | DOT2EQ
                | COLON
                | COLON2
                | EQ
                | EQ2
                | FAT_ARROW
                | BANG
                | NEQ
                | MINUS
                | THIN_ARROW
                | LTEQ
                | GTEQ
                | PLUSEQ
                | MINUSEQ
                | PIPEEQ
                | AMPEQ
                | CARETEQ
                | SLASHEQ
                | STAREQ
                | PERCENTEQ
                | AMP2
                | PIPE2
                | SHL
                | SHR
                | SHLEQ
                | SHREQ
        )
    }
    pub fn is_literal(self) -> bool {
        matches!(self, INT_NUMBER | FLOAT_NUMBER | CHAR | BYTE | STRING | BYTE_STRING)
    }
    pub fn from_keyword(ident: &str) -> Option<SyntaxKind> {
        let kw = match ident {
            "as" => AS_KW,
            "async" => ASYNC_KW,
            "await" => AWAIT_KW,
            "assert" => ASSERT_KW,
            "assume" => ASSUME_KW,
            "box" => BOX_KW,
            "break" => BREAK_KW,
            "const" => CONST_KW,
            "continue" => CONTINUE_KW,
            "crate" => CRATE_KW,
            "do" => DO_KW,
            "dyn" => DYN_KW,
            "else" => ELSE_KW,
            "enum" => ENUM_KW,
            "extern" => EXTERN_KW,
            "false" => FALSE_KW,
            "fn" => FN_KW,
            "for" => FOR_KW,
            "if" => IF_KW,
            "impl" => IMPL_KW,
            "in" => IN_KW,
            "let" => LET_KW,
            "loop" => LOOP_KW,
            "macro" => MACRO_KW,
            "match" => MATCH_KW,
            "mod" => MOD_KW,
            "move" => MOVE_KW,
            "mut" => MUT_KW,
            "pub" => PUB_KW,
            "ref" => REF_KW,
            "return" => RETURN_KW,
            "self" => SELF_KW,
            "Self" => SELF_TYPE_KW,
            "static" => STATIC_KW,
            "struct" => STRUCT_KW,
            "super" => SUPER_KW,
            "trait" => TRAIT_KW,
            "true" => TRUE_KW,
            "try" => TRY_KW,
            "type" => TYPE_KW,
            "unsafe" => UNSAFE_KW,
            "use" => USE_KW,
            "where" => WHERE_KW,
            "while" => WHILE_KW,
            "yield" => YIELD_KW,
            "int" => INT_KW,
            "bool" => BOOL_KW,
            "null" => NULL_KW,
            "result" => RESULT_KW,
            "ghost" => GHOST_KW,
            "pure" => PURE_KW,
            "requires" => REQUIRES_KW,
            "ensures" => ENSURES_KW,
            "decreases" => DECREASES_KW,
            "invariant" => INVARIANT_KW,
            "req" => REQ_KW,
            "ens" => ENS_KW,
            "dec" => DEC_KW,
            "inv" => INV_KW,
            "forall" => FORALL_KW,
            "exists" => EXISTS_KW,
            _ => return None,
        };
        Some(kw)
    }
    pub fn from_contextual_keyword(ident: &str) -> Option<SyntaxKind> {
        let kw = match ident {
            "auto" => AUTO_KW,
            "default" => DEFAULT_KW,
            "existential" => EXISTENTIAL_KW,
            "raw" => RAW_KW,
            "macro_rules" => MACRO_RULES_KW,
            "yeet" => YEET_KW,
            _ => return None,
        };
        Some(kw)
    }
    pub fn from_char(c: char) -> Option<SyntaxKind> {
        let tok = match c {
            ';' => SEMICOLON,
            ',' => COMMA,
            '(' => L_PAREN,
            ')' => R_PAREN,
            '{' => L_CURLY,
            '}' => R_CURLY,
            '[' => L_BRACK,
            ']' => R_BRACK,
            '<' => L_ANGLE,
            '>' => R_ANGLE,
            '@' => AT,
            '#' => POUND,
            '~' => TILDE,
            '?' => QUESTION,
            '$' => DOLLAR,
            '&' => AMP,
            '|' => PIPE,
            '+' => PLUS,
            '*' => STAR,
            '/' => SLASH,
            '^' => CARET,
            '%' => PERCENT,
            '_' => UNDERSCORE,
            '.' => DOT,
            ':' => COLON,
            '=' => EQ,
            '!' => BANG,
            '-' => MINUS,
            _ => return None,
        };
        Some(tok)
    }
}
#[macro_export]
macro_rules ! T { [;] => { $ crate :: SyntaxKind :: SEMICOLON } ; [,] => { $ crate :: SyntaxKind :: COMMA } ; ['('] => { $ crate :: SyntaxKind :: L_PAREN } ; [')'] => { $ crate :: SyntaxKind :: R_PAREN } ; ['{'] => { $ crate :: SyntaxKind :: L_CURLY } ; ['}'] => { $ crate :: SyntaxKind :: R_CURLY } ; ['['] => { $ crate :: SyntaxKind :: L_BRACK } ; [']'] => { $ crate :: SyntaxKind :: R_BRACK } ; [<] => { $ crate :: SyntaxKind :: L_ANGLE } ; [>] => { $ crate :: SyntaxKind :: R_ANGLE } ; [@] => { $ crate :: SyntaxKind :: AT } ; [#] => { $ crate :: SyntaxKind :: POUND } ; [~] => { $ crate :: SyntaxKind :: TILDE } ; [?] => { $ crate :: SyntaxKind :: QUESTION } ; [$] => { $ crate :: SyntaxKind :: DOLLAR } ; [&] => { $ crate :: SyntaxKind :: AMP } ; [|] => { $ crate :: SyntaxKind :: PIPE } ; [+] => { $ crate :: SyntaxKind :: PLUS } ; [*] => { $ crate :: SyntaxKind :: STAR } ; [/] => { $ crate :: SyntaxKind :: SLASH } ; [^] => { $ crate :: SyntaxKind :: CARET } ; [%] => { $ crate :: SyntaxKind :: PERCENT } ; [_] => { $ crate :: SyntaxKind :: UNDERSCORE } ; [.] => { $ crate :: SyntaxKind :: DOT } ; [..] => { $ crate :: SyntaxKind :: DOT2 } ; [...] => { $ crate :: SyntaxKind :: DOT3 } ; [..=] => { $ crate :: SyntaxKind :: DOT2EQ } ; [:] => { $ crate :: SyntaxKind :: COLON } ; [::] => { $ crate :: SyntaxKind :: COLON2 } ; [=] => { $ crate :: SyntaxKind :: EQ } ; [==] => { $ crate :: SyntaxKind :: EQ2 } ; [=>] => { $ crate :: SyntaxKind :: FAT_ARROW } ; [!] => { $ crate :: SyntaxKind :: BANG } ; [!=] => { $ crate :: SyntaxKind :: NEQ } ; [-] => { $ crate :: SyntaxKind :: MINUS } ; [->] => { $ crate :: SyntaxKind :: THIN_ARROW } ; [<=] => { $ crate :: SyntaxKind :: LTEQ } ; [>=] => { $ crate :: SyntaxKind :: GTEQ } ; [+=] => { $ crate :: SyntaxKind :: PLUSEQ } ; [-=] => { $ crate :: SyntaxKind :: MINUSEQ } ; [|=] => { $ crate :: SyntaxKind :: PIPEEQ } ; [&=] => { $ crate :: SyntaxKind :: AMPEQ } ; [^=] => { $ crate :: SyntaxKind :: CARETEQ } ; [/=] => { $ crate :: SyntaxKind :: SLASHEQ } ; [*=] => { $ crate :: SyntaxKind :: STAREQ } ; [%=] => { $ crate :: SyntaxKind :: PERCENTEQ } ; [&&] => { $ crate :: SyntaxKind :: AMP2 } ; [||] => { $ crate :: SyntaxKind :: PIPE2 } ; [<<] => { $ crate :: SyntaxKind :: SHL } ; [>>] => { $ crate :: SyntaxKind :: SHR } ; [<<=] => { $ crate :: SyntaxKind :: SHLEQ } ; [>>=] => { $ crate :: SyntaxKind :: SHREQ } ; [as] => { $ crate :: SyntaxKind :: AS_KW } ; [async] => { $ crate :: SyntaxKind :: ASYNC_KW } ; [await] => { $ crate :: SyntaxKind :: AWAIT_KW } ; [assert] => { $ crate :: SyntaxKind :: ASSERT_KW } ; [assume] => { $ crate :: SyntaxKind :: ASSUME_KW } ; [box] => { $ crate :: SyntaxKind :: BOX_KW } ; [break] => { $ crate :: SyntaxKind :: BREAK_KW } ; [const] => { $ crate :: SyntaxKind :: CONST_KW } ; [continue] => { $ crate :: SyntaxKind :: CONTINUE_KW } ; [crate] => { $ crate :: SyntaxKind :: CRATE_KW } ; [do] => { $ crate :: SyntaxKind :: DO_KW } ; [dyn] => { $ crate :: SyntaxKind :: DYN_KW } ; [else] => { $ crate :: SyntaxKind :: ELSE_KW } ; [enum] => { $ crate :: SyntaxKind :: ENUM_KW } ; [extern] => { $ crate :: SyntaxKind :: EXTERN_KW } ; [false] => { $ crate :: SyntaxKind :: FALSE_KW } ; [fn] => { $ crate :: SyntaxKind :: FN_KW } ; [for] => { $ crate :: SyntaxKind :: FOR_KW } ; [if] => { $ crate :: SyntaxKind :: IF_KW } ; [impl] => { $ crate :: SyntaxKind :: IMPL_KW } ; [in] => { $ crate :: SyntaxKind :: IN_KW } ; [let] => { $ crate :: SyntaxKind :: LET_KW } ; [loop] => { $ crate :: SyntaxKind :: LOOP_KW } ; [macro] => { $ crate :: SyntaxKind :: MACRO_KW } ; [match] => { $ crate :: SyntaxKind :: MATCH_KW } ; [mod] => { $ crate :: SyntaxKind :: MOD_KW } ; [move] => { $ crate :: SyntaxKind :: MOVE_KW } ; [mut] => { $ crate :: SyntaxKind :: MUT_KW } ; [pub] => { $ crate :: SyntaxKind :: PUB_KW } ; [ref] => { $ crate :: SyntaxKind :: REF_KW } ; [return] => { $ crate :: SyntaxKind :: RETURN_KW } ; [self] => { $ crate :: SyntaxKind :: SELF_KW } ; [Self] => { $ crate :: SyntaxKind :: SELF_TYPE_KW } ; [static] => { $ crate :: SyntaxKind :: STATIC_KW } ; [struct] => { $ crate :: SyntaxKind :: STRUCT_KW } ; [super] => { $ crate :: SyntaxKind :: SUPER_KW } ; [trait] => { $ crate :: SyntaxKind :: TRAIT_KW } ; [true] => { $ crate :: SyntaxKind :: TRUE_KW } ; [try] => { $ crate :: SyntaxKind :: TRY_KW } ; [type] => { $ crate :: SyntaxKind :: TYPE_KW } ; [unsafe] => { $ crate :: SyntaxKind :: UNSAFE_KW } ; [use] => { $ crate :: SyntaxKind :: USE_KW } ; [where] => { $ crate :: SyntaxKind :: WHERE_KW } ; [while] => { $ crate :: SyntaxKind :: WHILE_KW } ; [yield] => { $ crate :: SyntaxKind :: YIELD_KW } ; [int] => { $ crate :: SyntaxKind :: INT_KW } ; [bool] => { $ crate :: SyntaxKind :: BOOL_KW } ; [null] => { $ crate :: SyntaxKind :: NULL_KW } ; [result] => { $ crate :: SyntaxKind :: RESULT_KW } ; [ghost] => { $ crate :: SyntaxKind :: GHOST_KW } ; [pure] => { $ crate :: SyntaxKind :: PURE_KW } ; [requires] => { $ crate :: SyntaxKind :: REQUIRES_KW } ; [ensures] => { $ crate :: SyntaxKind :: ENSURES_KW } ; [decreases] => { $ crate :: SyntaxKind :: DECREASES_KW } ; [invariant] => { $ crate :: SyntaxKind :: INVARIANT_KW } ; [req] => { $ crate :: SyntaxKind :: REQ_KW } ; [ens] => { $ crate :: SyntaxKind :: ENS_KW } ; [dec] => { $ crate :: SyntaxKind :: DEC_KW } ; [inv] => { $ crate :: SyntaxKind :: INV_KW } ; [forall] => { $ crate :: SyntaxKind :: FORALL_KW } ; [exists] => { $ crate :: SyntaxKind :: EXISTS_KW } ; [auto] => { $ crate :: SyntaxKind :: AUTO_KW } ; [default] => { $ crate :: SyntaxKind :: DEFAULT_KW } ; [existential] => { $ crate :: SyntaxKind :: EXISTENTIAL_KW } ; [raw] => { $ crate :: SyntaxKind :: RAW_KW } ; [macro_rules] => { $ crate :: SyntaxKind :: MACRO_RULES_KW } ; [yeet] => { $ crate :: SyntaxKind :: YEET_KW } ; [lifetime_ident] => { $ crate :: SyntaxKind :: LIFETIME_IDENT } ; [ident] => { $ crate :: SyntaxKind :: IDENT } ; [shebang] => { $ crate :: SyntaxKind :: SHEBANG } ; }
pub use T; // Tokens

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Whitespace {
    pub(crate) syntax: SyntaxToken,
}
impl std::fmt::Display for Whitespace {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.syntax, f)
    }
}
impl AstToken for Whitespace {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == WHITESPACE
    }
    fn cast(syntax: SyntaxToken) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxToken {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Comment {
    pub(crate) syntax: SyntaxToken,
}
impl std::fmt::Display for Comment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.syntax, f)
    }
}
impl AstToken for Comment {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == COMMENT
    }
    fn cast(syntax: SyntaxToken) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxToken {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct String {
    pub(crate) syntax: SyntaxToken,
}
impl std::fmt::Display for String {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.syntax, f)
    }
}
impl AstToken for String {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == STRING
    }
    fn cast(syntax: SyntaxToken) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxToken {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ByteString {
    pub(crate) syntax: SyntaxToken,
}
impl std::fmt::Display for ByteString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.syntax, f)
    }
}
impl AstToken for ByteString {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == BYTE_STRING
    }
    fn cast(syntax: SyntaxToken) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxToken {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IntNumber {
    pub(crate) syntax: SyntaxToken,
}
impl std::fmt::Display for IntNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.syntax, f)
    }
}
impl AstToken for IntNumber {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == INT_NUMBER
    }
    fn cast(syntax: SyntaxToken) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxToken {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FloatNumber {
    pub(crate) syntax: SyntaxToken,
}
impl std::fmt::Display for FloatNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.syntax, f)
    }
}
impl AstToken for FloatNumber {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == FLOAT_NUMBER
    }
    fn cast(syntax: SyntaxToken) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxToken {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Char {
    pub(crate) syntax: SyntaxToken,
}
impl std::fmt::Display for Char {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.syntax, f)
    }
}
impl AstToken for Char {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == CHAR
    }
    fn cast(syntax: SyntaxToken) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxToken {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Byte {
    pub(crate) syntax: SyntaxToken,
}
impl std::fmt::Display for Byte {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.syntax, f)
    }
}
impl AstToken for Byte {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == BYTE
    }
    fn cast(syntax: SyntaxToken) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxToken {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ident {
    pub(crate) syntax: SyntaxToken,
}
impl std::fmt::Display for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.syntax, f)
    }
}
impl AstToken for Ident {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == IDENT
    }
    fn cast(syntax: SyntaxToken) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxToken {
        &self.syntax
    }
}
// Nodes

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SourceFile {
    pub(crate) syntax: SyntaxNode,
}
impl SourceFile {
    pub fn items(&self) -> AstChildren<Item> {
        support::children(&self.syntax)
    }
}
impl AstNode for SourceFile {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == SOURCE_FILE
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Const {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasAttrs for Const {}
impl crate::ast::HasName for Const {}
impl Const {
    pub fn const_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![const])
    }
    pub fn colon_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [:])
    }
    pub fn ty(&self) -> Option<Type> {
        support::child(&self.syntax)
    }
    pub fn eq_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [=])
    }
    pub fn initializer(&self) -> Option<Expr> {
        support::child(&self.syntax)
    }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [;])
    }
}
impl AstNode for Const {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == CONST
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Fn {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasAttrs for Fn {}
impl crate::ast::HasName for Fn {}
impl Fn {
    pub fn fn_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![fn])
    }
    pub fn param_list(&self) -> Option<ParamList> {
        support::child(&self.syntax)
    }
    pub fn thin_arrow_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [->])
    }
    pub fn ret(&self) -> Option<Type> {
        support::child(&self.syntax)
    }
    pub fn conditions(&self) -> AstChildren<Condition> {
        support::children(&self.syntax)
    }
    pub fn decreases(&self) -> Option<Decreases> {
        support::child(&self.syntax)
    }
    pub fn body(&self) -> Option<BlockExpr> {
        support::child(&self.syntax)
    }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [;])
    }
}
impl AstNode for Fn {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == FN
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Struct {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasAttrs for Struct {}
impl crate::ast::HasName for Struct {}
impl Struct {
    pub fn struct_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![struct])
    }
    pub fn generic_param_list(&self) -> Option<GenericParamList> {
        support::child(&self.syntax)
    }
    pub fn l_curly_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['{'])
    }
    pub fn struct_fields(&self) -> AstChildren<StructField> {
        support::children(&self.syntax)
    }
    pub fn r_curly_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['}'])
    }
}
impl AstNode for Struct {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == STRUCT
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeInvariant {
    pub(crate) syntax: SyntaxNode,
}
impl TypeInvariant {
    pub fn invariant_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![invariant])
    }
    pub fn generic_param_list(&self) -> Option<GenericParamList> {
        support::child(&self.syntax)
    }
    pub fn name_ref(&self) -> Option<NameRef> {
        support::child(&self.syntax)
    }
    pub fn generic_arg_list(&self) -> Option<GenericArgList> {
        support::child(&self.syntax)
    }
    pub fn block_expr(&self) -> Option<BlockExpr> {
        support::child(&self.syntax)
    }
}
impl AstNode for TypeInvariant {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == TYPE_INVARIANT
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Macro {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasName for Macro {}
impl Macro {
    pub fn macro_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![macro])
    }
    pub fn param_list(&self) -> Option<ParamList> {
        support::child(&self.syntax)
    }
    pub fn block_expr(&self) -> Option<BlockExpr> {
        support::child(&self.syntax)
    }
}
impl AstNode for Macro {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == MACRO
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Name {
    pub(crate) syntax: SyntaxNode,
}
impl Name {
    pub fn ident_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![ident])
    }
    pub fn self_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![self])
    }
}
impl AstNode for Name {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == NAME
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NameRef {
    pub(crate) syntax: SyntaxNode,
}
impl NameRef {
    pub fn ident_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![ident])
    }
    pub fn self_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![self])
    }
}
impl AstNode for NameRef {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == NAME_REF
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Attrs {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasAttrs for Attrs {}
impl Attrs {}
impl AstNode for Attrs {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == ATTRS
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParamList {
    pub(crate) syntax: SyntaxNode,
}
impl ParamList {
    pub fn l_paren_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['('])
    }
    pub fn params(&self) -> AstChildren<Param> {
        support::children(&self.syntax)
    }
    pub fn r_paren_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![')'])
    }
}
impl AstNode for ParamList {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == PARAM_LIST
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Decreases {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for Decreases {}
impl Decreases {
    pub fn decreases_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![decreases])
    }
    pub fn dec_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![dec])
    }
    pub fn underscore_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![_])
    }
}
impl AstNode for Decreases {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == DECREASES
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BlockExpr {
    pub(crate) syntax: SyntaxNode,
}
impl BlockExpr {
    pub fn l_curly_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['{'])
    }
    pub fn statements(&self) -> AstChildren<Stmt> {
        support::children(&self.syntax)
    }
    pub fn tail_expr(&self) -> Option<Expr> {
        support::child(&self.syntax)
    }
    pub fn r_curly_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['}'])
    }
}
impl AstNode for BlockExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == BLOCK_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Attr {
    pub(crate) syntax: SyntaxNode,
}
impl Attr {
    pub fn ghost_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![ghost])
    }
    pub fn pure_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![pure])
    }
}
impl AstNode for Attr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == ATTR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Param {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasAttrs for Param {}
impl crate::ast::HasName for Param {}
impl Param {
    pub fn colon_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [:])
    }
    pub fn ty(&self) -> Option<Type> {
        support::child(&self.syntax)
    }
    pub fn comma_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [,])
    }
}
impl AstNode for Param {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == PARAM
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Requires {
    pub(crate) syntax: SyntaxNode,
}
impl Requires {
    pub fn requires_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![requires])
    }
    pub fn req_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![req])
    }
    pub fn comma_exprs(&self) -> AstChildren<CommaExpr> {
        support::children(&self.syntax)
    }
}
impl AstNode for Requires {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == REQUIRES
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ensures {
    pub(crate) syntax: SyntaxNode,
}
impl Ensures {
    pub fn ensures_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![ensures])
    }
    pub fn ens_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![ens])
    }
    pub fn comma_exprs(&self) -> AstChildren<CommaExpr> {
        support::children(&self.syntax)
    }
}
impl AstNode for Ensures {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == ENSURES
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CommaExpr {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for CommaExpr {}
impl CommaExpr {
    pub fn comma_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [,])
    }
}
impl AstNode for CommaExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == COMMA_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericParamList {
    pub(crate) syntax: SyntaxNode,
}
impl GenericParamList {
    pub fn l_brack_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['['])
    }
    pub fn generic_params(&self) -> AstChildren<GenericParam> {
        support::children(&self.syntax)
    }
    pub fn r_brack_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![']'])
    }
}
impl AstNode for GenericParamList {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == GENERIC_PARAM_LIST
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructField {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasAttrs for StructField {}
impl crate::ast::HasName for StructField {}
impl StructField {
    pub fn colon_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [:])
    }
    pub fn ty(&self) -> Option<Type> {
        support::child(&self.syntax)
    }
    pub fn comma_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [,])
    }
}
impl AstNode for StructField {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == STRUCT_FIELD
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericArgList {
    pub(crate) syntax: SyntaxNode,
}
impl GenericArgList {
    pub fn l_brack_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['['])
    }
    pub fn generic_args(&self) -> AstChildren<GenericArg> {
        support::children(&self.syntax)
    }
    pub fn r_brack_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![']'])
    }
}
impl AstNode for GenericArgList {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == GENERIC_ARG_LIST
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericParam {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasName for GenericParam {}
impl GenericParam {
    pub fn comma_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [,])
    }
}
impl AstNode for GenericParam {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == GENERIC_PARAM
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NamedType {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasName for NamedType {}
impl NamedType {
    pub fn generic_arg_list(&self) -> Option<GenericArgList> {
        support::child(&self.syntax)
    }
}
impl AstNode for NamedType {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == NAMED_TYPE
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Primitive {
    pub(crate) syntax: SyntaxNode,
}
impl Primitive {
    pub fn int_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![int])
    }
    pub fn bool_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![bool])
    }
}
impl AstNode for Primitive {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == PRIMITIVE
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Optional {
    pub(crate) syntax: SyntaxNode,
}
impl Optional {
    pub fn question_mark_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [?])
    }
    pub fn ty(&self) -> Option<Type> {
        support::child(&self.syntax)
    }
}
impl AstNode for Optional {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == OPTIONAL
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ListType {
    pub(crate) syntax: SyntaxNode,
}
impl ListType {
    pub fn l_brack_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['['])
    }
    pub fn ty(&self) -> Option<Type> {
        support::child(&self.syntax)
    }
    pub fn r_brack_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![']'])
    }
}
impl AstNode for ListType {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == LIST_TYPE
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GhostType {
    pub(crate) syntax: SyntaxNode,
}
impl GhostType {
    pub fn ghost_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![ghost])
    }
    pub fn ty(&self) -> Option<Type> {
        support::child(&self.syntax)
    }
}
impl AstNode for GhostType {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == GHOST_TYPE
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RefType {
    pub(crate) syntax: SyntaxNode,
}
impl RefType {
    pub fn amp_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [&])
    }
    pub fn mut_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![mut])
    }
    pub fn ty(&self) -> Option<Type> {
        support::child(&self.syntax)
    }
}
impl AstNode for RefType {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == REF_TYPE
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GenericArg {
    pub(crate) syntax: SyntaxNode,
}
impl GenericArg {
    pub fn ty(&self) -> Option<Type> {
        support::child(&self.syntax)
    }
    pub fn comma_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [,])
    }
}
impl AstNode for GenericArg {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == GENERIC_ARG
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LetStmt {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasName for LetStmt {}
impl LetStmt {
    pub fn let_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![let])
    }
    pub fn colon_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [:])
    }
    pub fn ty(&self) -> Option<Type> {
        support::child(&self.syntax)
    }
    pub fn eq_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [=])
    }
    pub fn initializer(&self) -> Option<Expr> {
        support::child(&self.syntax)
    }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [;])
    }
}
impl AstNode for LetStmt {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == LET_STMT
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExprStmt {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for ExprStmt {}
impl ExprStmt {
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [;])
    }
}
impl AstNode for ExprStmt {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == EXPR_STMT
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AssertStmt {
    pub(crate) syntax: SyntaxNode,
}
impl AssertStmt {
    pub fn assert_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![assert])
    }
    pub fn comma_exprs(&self) -> AstChildren<CommaExpr> {
        support::children(&self.syntax)
    }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [;])
    }
}
impl AstNode for AssertStmt {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == ASSERT_STMT
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AssumeStmt {
    pub(crate) syntax: SyntaxNode,
}
impl AssumeStmt {
    pub fn assume_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![assume])
    }
    pub fn comma_exprs(&self) -> AstChildren<CommaExpr> {
        support::children(&self.syntax)
    }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [;])
    }
}
impl AstNode for AssumeStmt {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == ASSUME_STMT
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ReturnExpr {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for ReturnExpr {}
impl ReturnExpr {
    pub fn return_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![return])
    }
    pub fn semicolon_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [;])
    }
}
impl AstNode for ReturnExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == RETURN_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Invariant {
    pub(crate) syntax: SyntaxNode,
}
impl Invariant {
    pub fn invariant_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![invariant])
    }
    pub fn comma_exprs(&self) -> AstChildren<CommaExpr> {
        support::children(&self.syntax)
    }
}
impl AstNode for Invariant {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == INVARIANT
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Literal {
    pub(crate) syntax: SyntaxNode,
}
impl Literal {}
impl AstNode for Literal {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == LITERAL
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IfExpr {
    pub(crate) syntax: SyntaxNode,
}
impl IfExpr {
    pub fn if_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![if])
    }
    pub fn else_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![else])
    }
}
impl AstNode for IfExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == IF_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct WhileExpr {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for WhileExpr {}
impl WhileExpr {
    pub fn while_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![while])
    }
    pub fn invariants(&self) -> AstChildren<Invariant> {
        support::children(&self.syntax)
    }
    pub fn decreases(&self) -> Option<Decreases> {
        support::child(&self.syntax)
    }
    pub fn block_expr(&self) -> Option<BlockExpr> {
        support::child(&self.syntax)
    }
}
impl AstNode for WhileExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == WHILE_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ForExpr {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasName for ForExpr {}
impl crate::ast::HasExpr for ForExpr {}
impl ForExpr {
    pub fn for_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![for])
    }
    pub fn in_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![in])
    }
    pub fn invariants(&self) -> AstChildren<Invariant> {
        support::children(&self.syntax)
    }
    pub fn block_expr(&self) -> Option<BlockExpr> {
        support::child(&self.syntax)
    }
}
impl AstNode for ForExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == FOR_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PrefixExpr {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for PrefixExpr {}
impl PrefixExpr {}
impl AstNode for PrefixExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == PREFIX_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BinExpr {
    pub(crate) syntax: SyntaxNode,
}
impl BinExpr {}
impl AstNode for BinExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == BIN_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RangeExpr {
    pub(crate) syntax: SyntaxNode,
}
impl RangeExpr {
    pub fn dotdot_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![..])
    }
}
impl AstNode for RangeExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == RANGE_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CallExpr {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for CallExpr {}
impl CallExpr {
    pub fn arg_list(&self) -> Option<ArgList> {
        support::child(&self.syntax)
    }
}
impl AstNode for CallExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == CALL_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ListExpr {
    pub(crate) syntax: SyntaxNode,
}
impl ListExpr {
    pub fn l_brack_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['['])
    }
    pub fn comma_exprs(&self) -> AstChildren<CommaExpr> {
        support::children(&self.syntax)
    }
    pub fn r_brack_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![']'])
    }
}
impl AstNode for ListExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == LIST_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IndexExpr {
    pub(crate) syntax: SyntaxNode,
}
impl IndexExpr {
    pub fn l_brack_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['['])
    }
    pub fn r_brack_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![']'])
    }
}
impl AstNode for IndexExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == INDEX_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NotNullExpr {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for NotNullExpr {}
impl NotNullExpr {
    pub fn excl_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![!])
    }
}
impl AstNode for NotNullExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == NOT_NULL_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldExpr {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for FieldExpr {}
impl FieldExpr {
    pub fn dot_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [.])
    }
    pub fn field(&self) -> Option<NameRef> {
        support::child(&self.syntax)
    }
}
impl AstNode for FieldExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == FIELD_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructExpr {
    pub(crate) syntax: SyntaxNode,
}
impl StructExpr {
    pub fn name_ref(&self) -> Option<NameRef> {
        support::child(&self.syntax)
    }
    pub fn l_curly_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['{'])
    }
    pub fn fields(&self) -> AstChildren<StructExprField> {
        support::children(&self.syntax)
    }
    pub fn r_curly_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['}'])
    }
}
impl AstNode for StructExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == STRUCT_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParenExpr {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for ParenExpr {}
impl ParenExpr {
    pub fn l_paren_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['('])
    }
    pub fn r_paren_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![')'])
    }
}
impl AstNode for ParenExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == PAREN_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RefExpr {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for RefExpr {}
impl RefExpr {
    pub fn amp_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [&])
    }
    pub fn mut_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![mut])
    }
}
impl AstNode for RefExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == REF_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IdentExpr {
    pub(crate) syntax: SyntaxNode,
}
impl IdentExpr {
    pub fn name_ref(&self) -> Option<NameRef> {
        support::child(&self.syntax)
    }
}
impl AstNode for IdentExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == IDENT_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NullExpr {
    pub(crate) syntax: SyntaxNode,
}
impl NullExpr {
    pub fn null_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![null])
    }
}
impl AstNode for NullExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == NULL_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ResultExpr {
    pub(crate) syntax: SyntaxNode,
}
impl ResultExpr {
    pub fn result_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![result])
    }
}
impl AstNode for ResultExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == RESULT_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QuantifierExpr {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for QuantifierExpr {}
impl QuantifierExpr {
    pub fn quantifier(&self) -> Option<Quantifier> {
        support::child(&self.syntax)
    }
    pub fn quantifier_over(&self) -> Option<QuantifierOver> {
        support::child(&self.syntax)
    }
}
impl AstNode for QuantifierExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == QUANTIFIER_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ArgList {
    pub(crate) syntax: SyntaxNode,
}
impl ArgList {
    pub fn l_paren_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T!['('])
    }
    pub fn args(&self) -> AstChildren<Arg> {
        support::children(&self.syntax)
    }
    pub fn r_paren_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![')'])
    }
}
impl AstNode for ArgList {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == ARG_LIST
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Arg {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for Arg {}
impl Arg {
    pub fn comma_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [,])
    }
}
impl AstNode for Arg {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == ARG
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructExprField {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasExpr for StructExprField {}
impl StructExprField {
    pub fn name_ref(&self) -> Option<NameRef> {
        support::child(&self.syntax)
    }
    pub fn colon_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [:])
    }
    pub fn comma_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T ! [,])
    }
}
impl AstNode for StructExprField {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == STRUCT_EXPR_FIELD
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Quantifier {
    pub(crate) syntax: SyntaxNode,
}
impl Quantifier {
    pub fn forall_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![forall])
    }
    pub fn exists_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![exists])
    }
}
impl AstNode for Quantifier {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == QUANTIFIER
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NameInExpr {
    pub(crate) syntax: SyntaxNode,
}
impl crate::ast::HasName for NameInExpr {}
impl crate::ast::HasExpr for NameInExpr {}
impl NameInExpr {
    pub fn in_token(&self) -> Option<SyntaxToken> {
        support::token(&self.syntax, T![in])
    }
}
impl AstNode for NameInExpr {
    fn can_cast(kind: SyntaxKind) -> bool {
        kind == NAME_IN_EXPR
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        if Self::can_cast(syntax.kind()) {
            Some(Self { syntax })
        } else {
            None
        }
    }
    fn syntax(&self) -> &SyntaxNode {
        &self.syntax
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Item {
    Const(Const),
    Fn(Fn),
    Struct(Struct),
    TypeInvariant(TypeInvariant),
    Macro(Macro),
}
impl From<Const> for Item {
    fn from(node: Const) -> Item {
        Item::Const(node)
    }
}
impl From<Fn> for Item {
    fn from(node: Fn) -> Item {
        Item::Fn(node)
    }
}
impl From<Struct> for Item {
    fn from(node: Struct) -> Item {
        Item::Struct(node)
    }
}
impl From<TypeInvariant> for Item {
    fn from(node: TypeInvariant) -> Item {
        Item::TypeInvariant(node)
    }
}
impl From<Macro> for Item {
    fn from(node: Macro) -> Item {
        Item::Macro(node)
    }
}
impl AstNode for Item {
    fn can_cast(kind: SyntaxKind) -> bool {
        matches!(kind, CONST | FN | STRUCT | TYPE_INVARIANT | MACRO)
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        let res = match syntax.kind() {
            CONST => Item::Const(Const { syntax }),
            FN => Item::Fn(Fn { syntax }),
            STRUCT => Item::Struct(Struct { syntax }),
            TYPE_INVARIANT => Item::TypeInvariant(TypeInvariant { syntax }),
            MACRO => Item::Macro(Macro { syntax }),
            _ => return None,
        };
        Some(res)
    }
    fn syntax(&self) -> &SyntaxNode {
        match self {
            Item::Const(it) => &it.syntax,
            Item::Fn(it) => &it.syntax,
            Item::Struct(it) => &it.syntax,
            Item::TypeInvariant(it) => &it.syntax,
            Item::Macro(it) => &it.syntax,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    NamedType(NamedType),
    Primitive(Primitive),
    Optional(Optional),
    ListType(ListType),
    GhostType(GhostType),
    RefType(RefType),
}
impl From<NamedType> for Type {
    fn from(node: NamedType) -> Type {
        Type::NamedType(node)
    }
}
impl From<Primitive> for Type {
    fn from(node: Primitive) -> Type {
        Type::Primitive(node)
    }
}
impl From<Optional> for Type {
    fn from(node: Optional) -> Type {
        Type::Optional(node)
    }
}
impl From<ListType> for Type {
    fn from(node: ListType) -> Type {
        Type::ListType(node)
    }
}
impl From<GhostType> for Type {
    fn from(node: GhostType) -> Type {
        Type::GhostType(node)
    }
}
impl From<RefType> for Type {
    fn from(node: RefType) -> Type {
        Type::RefType(node)
    }
}
impl AstNode for Type {
    fn can_cast(kind: SyntaxKind) -> bool {
        matches!(kind, NAMED_TYPE | PRIMITIVE | OPTIONAL | LIST_TYPE | GHOST_TYPE | REF_TYPE)
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        let res = match syntax.kind() {
            NAMED_TYPE => Type::NamedType(NamedType { syntax }),
            PRIMITIVE => Type::Primitive(Primitive { syntax }),
            OPTIONAL => Type::Optional(Optional { syntax }),
            LIST_TYPE => Type::ListType(ListType { syntax }),
            GHOST_TYPE => Type::GhostType(GhostType { syntax }),
            REF_TYPE => Type::RefType(RefType { syntax }),
            _ => return None,
        };
        Some(res)
    }
    fn syntax(&self) -> &SyntaxNode {
        match self {
            Type::NamedType(it) => &it.syntax,
            Type::Primitive(it) => &it.syntax,
            Type::Optional(it) => &it.syntax,
            Type::ListType(it) => &it.syntax,
            Type::GhostType(it) => &it.syntax,
            Type::RefType(it) => &it.syntax,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Literal(Literal),
    IfExpr(IfExpr),
    ReturnExpr(ReturnExpr),
    WhileExpr(WhileExpr),
    ForExpr(ForExpr),
    PrefixExpr(PrefixExpr),
    BinExpr(BinExpr),
    BlockExpr(BlockExpr),
    RangeExpr(RangeExpr),
    CallExpr(CallExpr),
    ListExpr(ListExpr),
    IndexExpr(IndexExpr),
    NotNullExpr(NotNullExpr),
    FieldExpr(FieldExpr),
    StructExpr(StructExpr),
    ParenExpr(ParenExpr),
    RefExpr(RefExpr),
    IdentExpr(IdentExpr),
    NullExpr(NullExpr),
    ResultExpr(ResultExpr),
    QuantifierExpr(QuantifierExpr),
}
impl From<Literal> for Expr {
    fn from(node: Literal) -> Expr {
        Expr::Literal(node)
    }
}
impl From<IfExpr> for Expr {
    fn from(node: IfExpr) -> Expr {
        Expr::IfExpr(node)
    }
}
impl From<ReturnExpr> for Expr {
    fn from(node: ReturnExpr) -> Expr {
        Expr::ReturnExpr(node)
    }
}
impl From<WhileExpr> for Expr {
    fn from(node: WhileExpr) -> Expr {
        Expr::WhileExpr(node)
    }
}
impl From<ForExpr> for Expr {
    fn from(node: ForExpr) -> Expr {
        Expr::ForExpr(node)
    }
}
impl From<PrefixExpr> for Expr {
    fn from(node: PrefixExpr) -> Expr {
        Expr::PrefixExpr(node)
    }
}
impl From<BinExpr> for Expr {
    fn from(node: BinExpr) -> Expr {
        Expr::BinExpr(node)
    }
}
impl From<BlockExpr> for Expr {
    fn from(node: BlockExpr) -> Expr {
        Expr::BlockExpr(node)
    }
}
impl From<RangeExpr> for Expr {
    fn from(node: RangeExpr) -> Expr {
        Expr::RangeExpr(node)
    }
}
impl From<CallExpr> for Expr {
    fn from(node: CallExpr) -> Expr {
        Expr::CallExpr(node)
    }
}
impl From<ListExpr> for Expr {
    fn from(node: ListExpr) -> Expr {
        Expr::ListExpr(node)
    }
}
impl From<IndexExpr> for Expr {
    fn from(node: IndexExpr) -> Expr {
        Expr::IndexExpr(node)
    }
}
impl From<NotNullExpr> for Expr {
    fn from(node: NotNullExpr) -> Expr {
        Expr::NotNullExpr(node)
    }
}
impl From<FieldExpr> for Expr {
    fn from(node: FieldExpr) -> Expr {
        Expr::FieldExpr(node)
    }
}
impl From<StructExpr> for Expr {
    fn from(node: StructExpr) -> Expr {
        Expr::StructExpr(node)
    }
}
impl From<ParenExpr> for Expr {
    fn from(node: ParenExpr) -> Expr {
        Expr::ParenExpr(node)
    }
}
impl From<RefExpr> for Expr {
    fn from(node: RefExpr) -> Expr {
        Expr::RefExpr(node)
    }
}
impl From<IdentExpr> for Expr {
    fn from(node: IdentExpr) -> Expr {
        Expr::IdentExpr(node)
    }
}
impl From<NullExpr> for Expr {
    fn from(node: NullExpr) -> Expr {
        Expr::NullExpr(node)
    }
}
impl From<ResultExpr> for Expr {
    fn from(node: ResultExpr) -> Expr {
        Expr::ResultExpr(node)
    }
}
impl From<QuantifierExpr> for Expr {
    fn from(node: QuantifierExpr) -> Expr {
        Expr::QuantifierExpr(node)
    }
}
impl AstNode for Expr {
    fn can_cast(kind: SyntaxKind) -> bool {
        matches!(
            kind,
            LITERAL
                | IF_EXPR
                | RETURN_EXPR
                | WHILE_EXPR
                | FOR_EXPR
                | PREFIX_EXPR
                | BIN_EXPR
                | BLOCK_EXPR
                | RANGE_EXPR
                | CALL_EXPR
                | LIST_EXPR
                | INDEX_EXPR
                | NOT_NULL_EXPR
                | FIELD_EXPR
                | STRUCT_EXPR
                | PAREN_EXPR
                | REF_EXPR
                | IDENT_EXPR
                | NULL_EXPR
                | RESULT_EXPR
                | QUANTIFIER_EXPR
        )
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        let res = match syntax.kind() {
            LITERAL => Expr::Literal(Literal { syntax }),
            IF_EXPR => Expr::IfExpr(IfExpr { syntax }),
            RETURN_EXPR => Expr::ReturnExpr(ReturnExpr { syntax }),
            WHILE_EXPR => Expr::WhileExpr(WhileExpr { syntax }),
            FOR_EXPR => Expr::ForExpr(ForExpr { syntax }),
            PREFIX_EXPR => Expr::PrefixExpr(PrefixExpr { syntax }),
            BIN_EXPR => Expr::BinExpr(BinExpr { syntax }),
            BLOCK_EXPR => Expr::BlockExpr(BlockExpr { syntax }),
            RANGE_EXPR => Expr::RangeExpr(RangeExpr { syntax }),
            CALL_EXPR => Expr::CallExpr(CallExpr { syntax }),
            LIST_EXPR => Expr::ListExpr(ListExpr { syntax }),
            INDEX_EXPR => Expr::IndexExpr(IndexExpr { syntax }),
            NOT_NULL_EXPR => Expr::NotNullExpr(NotNullExpr { syntax }),
            FIELD_EXPR => Expr::FieldExpr(FieldExpr { syntax }),
            STRUCT_EXPR => Expr::StructExpr(StructExpr { syntax }),
            PAREN_EXPR => Expr::ParenExpr(ParenExpr { syntax }),
            REF_EXPR => Expr::RefExpr(RefExpr { syntax }),
            IDENT_EXPR => Expr::IdentExpr(IdentExpr { syntax }),
            NULL_EXPR => Expr::NullExpr(NullExpr { syntax }),
            RESULT_EXPR => Expr::ResultExpr(ResultExpr { syntax }),
            QUANTIFIER_EXPR => Expr::QuantifierExpr(QuantifierExpr { syntax }),
            _ => return None,
        };
        Some(res)
    }
    fn syntax(&self) -> &SyntaxNode {
        match self {
            Expr::Literal(it) => &it.syntax,
            Expr::IfExpr(it) => &it.syntax,
            Expr::ReturnExpr(it) => &it.syntax,
            Expr::WhileExpr(it) => &it.syntax,
            Expr::ForExpr(it) => &it.syntax,
            Expr::PrefixExpr(it) => &it.syntax,
            Expr::BinExpr(it) => &it.syntax,
            Expr::BlockExpr(it) => &it.syntax,
            Expr::RangeExpr(it) => &it.syntax,
            Expr::CallExpr(it) => &it.syntax,
            Expr::ListExpr(it) => &it.syntax,
            Expr::IndexExpr(it) => &it.syntax,
            Expr::NotNullExpr(it) => &it.syntax,
            Expr::FieldExpr(it) => &it.syntax,
            Expr::StructExpr(it) => &it.syntax,
            Expr::ParenExpr(it) => &it.syntax,
            Expr::RefExpr(it) => &it.syntax,
            Expr::IdentExpr(it) => &it.syntax,
            Expr::NullExpr(it) => &it.syntax,
            Expr::ResultExpr(it) => &it.syntax,
            Expr::QuantifierExpr(it) => &it.syntax,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Condition {
    Requires(Requires),
    Ensures(Ensures),
}
impl From<Requires> for Condition {
    fn from(node: Requires) -> Condition {
        Condition::Requires(node)
    }
}
impl From<Ensures> for Condition {
    fn from(node: Ensures) -> Condition {
        Condition::Ensures(node)
    }
}
impl AstNode for Condition {
    fn can_cast(kind: SyntaxKind) -> bool {
        matches!(kind, REQUIRES | ENSURES)
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        let res = match syntax.kind() {
            REQUIRES => Condition::Requires(Requires { syntax }),
            ENSURES => Condition::Ensures(Ensures { syntax }),
            _ => return None,
        };
        Some(res)
    }
    fn syntax(&self) -> &SyntaxNode {
        match self {
            Condition::Requires(it) => &it.syntax,
            Condition::Ensures(it) => &it.syntax,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Stmt {
    LetStmt(LetStmt),
    Item(Item),
    ExprStmt(ExprStmt),
    AssertStmt(AssertStmt),
    AssumeStmt(AssumeStmt),
}
impl From<LetStmt> for Stmt {
    fn from(node: LetStmt) -> Stmt {
        Stmt::LetStmt(node)
    }
}
impl From<Item> for Stmt {
    fn from(node: Item) -> Stmt {
        Stmt::Item(node)
    }
}
impl From<ExprStmt> for Stmt {
    fn from(node: ExprStmt) -> Stmt {
        Stmt::ExprStmt(node)
    }
}
impl From<AssertStmt> for Stmt {
    fn from(node: AssertStmt) -> Stmt {
        Stmt::AssertStmt(node)
    }
}
impl From<AssumeStmt> for Stmt {
    fn from(node: AssumeStmt) -> Stmt {
        Stmt::AssumeStmt(node)
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum IfExprElse {
    IfExpr(IfExpr),
    BlockExpr(BlockExpr),
}
impl From<IfExpr> for IfExprElse {
    fn from(node: IfExpr) -> IfExprElse {
        IfExprElse::IfExpr(node)
    }
}
impl From<BlockExpr> for IfExprElse {
    fn from(node: BlockExpr) -> IfExprElse {
        IfExprElse::BlockExpr(node)
    }
}
impl AstNode for IfExprElse {
    fn can_cast(kind: SyntaxKind) -> bool {
        matches!(kind, IF_EXPR | BLOCK_EXPR)
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        let res = match syntax.kind() {
            IF_EXPR => IfExprElse::IfExpr(IfExpr { syntax }),
            BLOCK_EXPR => IfExprElse::BlockExpr(BlockExpr { syntax }),
            _ => return None,
        };
        Some(res)
    }
    fn syntax(&self) -> &SyntaxNode {
        match self {
            IfExprElse::IfExpr(it) => &it.syntax,
            IfExprElse::BlockExpr(it) => &it.syntax,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum QuantifierOver {
    ParamList(ParamList),
    NameInExpr(NameInExpr),
}
impl From<ParamList> for QuantifierOver {
    fn from(node: ParamList) -> QuantifierOver {
        QuantifierOver::ParamList(node)
    }
}
impl From<NameInExpr> for QuantifierOver {
    fn from(node: NameInExpr) -> QuantifierOver {
        QuantifierOver::NameInExpr(node)
    }
}
impl AstNode for QuantifierOver {
    fn can_cast(kind: SyntaxKind) -> bool {
        matches!(kind, PARAM_LIST | NAME_IN_EXPR)
    }
    fn cast(syntax: SyntaxNode) -> Option<Self> {
        let res = match syntax.kind() {
            PARAM_LIST => QuantifierOver::ParamList(ParamList { syntax }),
            NAME_IN_EXPR => QuantifierOver::NameInExpr(NameInExpr { syntax }),
            _ => return None,
        };
        Some(res)
    }
    fn syntax(&self) -> &SyntaxNode {
        match self {
            QuantifierOver::ParamList(it) => &it.syntax,
            QuantifierOver::NameInExpr(it) => &it.syntax,
        }
    }
}
impl std::fmt::Display for Item {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Condition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for IfExprElse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for QuantifierOver {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for SourceFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Const {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Fn {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Struct {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for TypeInvariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Macro {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for NameRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Attrs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for ParamList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Decreases {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for BlockExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Attr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Requires {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Ensures {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for CommaExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for GenericParamList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for StructField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for GenericArgList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for GenericParam {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for NamedType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Primitive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Optional {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for ListType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for GhostType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for RefType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for GenericArg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for LetStmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for ExprStmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for AssertStmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for AssumeStmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for ReturnExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Invariant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for IfExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for WhileExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for ForExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for PrefixExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for BinExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for RangeExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for CallExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for ListExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for IndexExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for NotNullExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for FieldExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for StructExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for ParenExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for RefExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for IdentExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for NullExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for ResultExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for QuantifierExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for ArgList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Arg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for StructExprField {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for Quantifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
impl std::fmt::Display for NameInExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(self.syntax(), f)
    }
}
