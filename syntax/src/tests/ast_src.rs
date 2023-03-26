//! Defines input for code generation process.

pub(crate) struct KindsSrc<'a> {
    pub(crate) punct: &'a [(&'a str, &'a str)],
    pub(crate) keywords: &'a [&'a str],
    pub(crate) contextual_keywords: &'a [&'a str],
    pub(crate) literals: &'a [&'a str],
    pub(crate) tokens: &'a [&'a str],
    pub(crate) nodes: &'a [&'a str],
}

pub(crate) const KINDS_SRC: KindsSrc<'_> = KindsSrc {
    punct: &[
        (";", "SEMICOLON"),
        (",", "COMMA"),
        ("(", "L_PAREN"),
        (")", "R_PAREN"),
        ("{", "L_CURLY"),
        ("}", "R_CURLY"),
        ("[", "L_BRACK"),
        ("]", "R_BRACK"),
        ("<", "L_ANGLE"),
        (">", "R_ANGLE"),
        ("@", "AT"),
        ("#", "POUND"),
        ("~", "TILDE"),
        ("?", "QUESTION"),
        ("$", "DOLLAR"),
        ("&", "AMP"),
        ("|", "PIPE"),
        ("+", "PLUS"),
        ("*", "STAR"),
        ("/", "SLASH"),
        ("^", "CARET"),
        ("%", "PERCENT"),
        ("_", "UNDERSCORE"),
        (".", "DOT"),
        ("..", "DOT2"),
        ("...", "DOT3"),
        ("..=", "DOT2EQ"),
        (":", "COLON"),
        ("::", "COLON2"),
        ("=", "EQ"),
        ("==", "EQ2"),
        ("=>", "FAT_ARROW"),
        ("!", "BANG"),
        ("!=", "NEQ"),
        ("-", "MINUS"),
        ("->", "THIN_ARROW"),
        ("<=", "LTEQ"),
        (">=", "GTEQ"),
        ("+=", "PLUSEQ"),
        ("-=", "MINUSEQ"),
        ("|=", "PIPEEQ"),
        ("&=", "AMPEQ"),
        ("^=", "CARETEQ"),
        ("/=", "SLASHEQ"),
        ("*=", "STAREQ"),
        ("%=", "PERCENTEQ"),
        ("&&", "AMP2"),
        ("||", "PIPE2"),
        ("<<", "SHL"),
        (">>", "SHR"),
        ("<<=", "SHLEQ"),
        (">>=", "SHREQ"),
    ],
    keywords: &[
        "as",
        "async",
        "await",
        "assert",
        "assume",
        "box",
        "break",
        "const",
        "continue",
        "crate",
        "do",
        "dyn",
        "else",
        "enum",
        "extern",
        "false",
        "fn",
        "for",
        "if",
        "impl",
        "in",
        "let",
        "loop",
        "macro",
        "match",
        "mod",
        "move",
        "mut",
        "pub",
        "ref",
        "return",
        "self",
        "Self",
        "static",
        "struct",
        "super",
        "trait",
        "true",
        "try",
        "type",
        "unsafe",
        "use",
        "where",
        "while",
        "yield",
        "int",
        "bool",
        "null",
        "result",
        "ghost",
        "pure",
        "requires",
        "ensures",
        "forall",
        "exists",
        "invariant",
    ],
    contextual_keywords: &[
        "auto",
        "default",
        "existential",
        "raw",
        "macro_rules",
        "yeet",
    ],
    literals: &[
        "INT_NUMBER",
        "FLOAT_NUMBER",
        "CHAR",
        "BYTE",
        "STRING",
        "BYTE_STRING",
    ],
    tokens: &[
        "ERROR",
        "IDENT",
        "WHITESPACE",
        "LIFETIME_IDENT",
        "COMMENT",
        "SHEBANG",
    ],
    nodes: &[
        "SOURCE_FILE",
        "STRUCT",
        "ENUM",
        "FN",
        "MACRO",
        "RET_TYPE",
        "EXTERN_CRATE",
        "MODULE",
        "USE",
        "STATIC",
        "CONST",
        "TRAIT",
        "IMPL",
        "TYPE_ALIAS",
        "MACRO_CALL",
        "MACRO_RULES",
        "MACRO_ARM",
        "TOKEN_TREE",
        "MACRO_DEF",
        "NAMED_TYPE",
        "PAREN_TYPE",
        "TUPLE_TYPE",
        "MACRO_TYPE",
        "NEVER_TYPE",
        "PATH_TYPE",
        "PTR_TYPE",
        "ARRAY_TYPE",
        "SLICE_TYPE",
        "REF_TYPE",
        "GHOST_TYPE",
        "INFER_TYPE",
        "FN_PTR_TYPE",
        "FOR_TYPE",
        "IMPL_TRAIT_TYPE",
        "DYN_TRAIT_TYPE",
        "OR_PAT",
        "PAREN_PAT",
        "REF_PAT",
        "BOX_PAT",
        "IDENT_PAT",
        "WILDCARD_PAT",
        "REST_PAT",
        "PATH_PAT",
        "RECORD_PAT",
        "RECORD_PAT_FIELD_LIST",
        "RECORD_PAT_FIELD",
        "TUPLE_STRUCT_PAT",
        "TUPLE_PAT",
        "SLICE_PAT",
        "RANGE_PAT",
        "LITERAL_PAT",
        "MACRO_PAT",
        "CONST_BLOCK_PAT",
        // atoms
        "TUPLE_EXPR",
        "ARRAY_EXPR",
        "PAREN_EXPR",
        "PATH_EXPR",
        "IDENT_EXPR",
        "NULL_EXPR",
        "RESULT_EXPR",
        "CLOSURE_EXPR",
        "QUANTIFIER_EXPR",
        "QUANTIFIER",
        "IF_EXPR",
        "WHILE_EXPR",
        "LOOP_EXPR",
        "FOR_EXPR",
        "CONTINUE_EXPR",
        "BREAK_EXPR",
        "LABEL",
        "BLOCK",
        "STMT_LIST",
        "RETURN_STMT",
        "WHILE_STMT",
        "YIELD_EXPR",
        "YEET_EXPR",
        "LET_EXPR",
        "UNDERSCORE_EXPR",
        "MACRO_EXPR",
        "MATCH_EXPR",
        "MATCH_ARM_LIST",
        "MATCH_ARM",
        "MATCH_GUARD",
        "RECORD_EXPR",
        "RECORD_EXPR_FIELD_LIST",
        "RECORD_EXPR_FIELD",
        "STRUCT_EXPR_FIELD",
        "COMMA_EXPR",
        "BOX_EXPR",
        // postfix
        "CALL_EXPR",
        "STRUCT_EXPR",
        "INDEX_EXPR",
        "METHOD_CALL_EXPR",
        "FIELD_EXPR",
        "AWAIT_EXPR",
        "TRY_EXPR",
        "CAST_EXPR",
        // unary
        "REF_EXPR",
        "PREFIX_EXPR",
        "RANGE_EXPR", // just weird
        "BIN_EXPR",
        "EXTERN_BLOCK",
        "EXTERN_ITEM_LIST",
        "VARIANT",
        "RECORD_FIELD_LIST",
        "RECORD_FIELD",
        "STRUCT_FIELD",
        "TUPLE_FIELD_LIST",
        "TUPLE_FIELD",
        "VARIANT_LIST",
        "ITEM_LIST",
        "ASSOC_ITEM_LIST",
        "ATTR",
        "META",
        "FN_ATTR",
        "USE_TREE",
        "USE_TREE_LIST",
        "PATH",
        "PATH_SEGMENT",
        "LITERAL",
        "RENAME",
        "VISIBILITY",
        "WHERE_CLAUSE",
        "WHERE_PRED",
        "CONDITION",
        "REQUIRES",
        "ENSURES",
        "INVARIANT",
        "ABI",
        "NAME",
        "NAME_REF",
        "PRIMITIVE",
        "OPTIONAL",
        "ASSUME_STMT",
        "ASSERT_STMT",
        "LET_STMT",
        "LET_ELSE",
        "EXPR_STMT",
        "GENERIC_PARAM_LIST",
        "GENERIC_PARAM",
        "LIFETIME_PARAM",
        "TYPE_PARAM",
        "CONST_PARAM",
        "GENERIC_ARG_LIST",
        "LIFETIME",
        "LIFETIME_ARG",
        "TYPE_ARG",
        "ASSOC_TYPE_ARG",
        "CONST_ARG",
        "PARAM_LIST",
        "PARAM",
        "SELF_PARAM",
        "ARG_LIST",
        "ARG",
        "TYPE_BOUND",
        "TYPE_BOUND_LIST",
        // macro related
        "MACRO_ITEMS",
        "MACRO_STMTS",
    ],
};

#[derive(Default, Debug)]
pub(crate) struct AstSrc {
    pub(crate) tokens: Vec<String>,
    pub(crate) nodes: Vec<AstNodeSrc>,
    pub(crate) enums: Vec<AstEnumSrc>,
}

#[derive(Debug)]
pub(crate) struct AstNodeSrc {
    // pub(crate) doc: Vec<String>,
    pub(crate) name: String,
    // pub(crate) traits: Vec<String>,
    pub(crate) fields: Vec<Field>,
}
impl AstNodeSrc {
    pub(crate) fn remove_field(&mut self, to_remove: Vec<usize>) {
        to_remove.into_iter().rev().for_each(|idx| {
            self.fields.remove(idx);
        });
    }
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Field {
    Token(String),
    Node {
        name: String,
        ty: String,
        cardinality: Cardinality,
    },
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Cardinality {
    Optional,
    Many,
}

#[derive(Debug)]
pub(crate) struct AstEnumSrc {
    // pub(crate) doc: Vec<String>,
    pub(crate) name: String,
    // pub(crate) traits: Vec<String>,
    pub(crate) variants: Vec<String>,
}
