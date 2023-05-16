use std::{fs, io::Write, path::PathBuf};

use heck::{ToShoutySnakeCase, ToSnakeCase};
use itertools::Itertools;
use proc_macro2::{Punct, Spacing};
use quote::{format_ident, quote};
use ungrammar::{Grammar, Rule};

use super::ast_src::{AstEnumSrc, AstNodeSrc, AstSrc, Cardinality, Field, KindsSrc, KINDS_SRC};

#[test]
fn sourcegen_ast() -> color_eyre::Result<()> {
    let grammar: Grammar = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/mist.ungram"))
        .parse()
        .unwrap();

    let preamble = quote! {
        #![allow(bad_style, missing_docs, unreachable_pub, dead_code, unused)]

        use crate::{SyntaxToken, SyntaxNode, SyntaxNodeChildren, support};
        use support::{AstNode, AstChildren, AstToken};
    };

    let ast = lower(&grammar);
    eprintln!("{ast:#?}");

    let kinds = generate_syntax_kinds(KINDS_SRC);
    let tokens = generate_tokens(&ast);
    let nodes = generate_nodes(&ast);

    let output_path = PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/src/ast/generated.rs"));
    let backup_path = output_path.with_extension("rs.bak");
    fs::copy(&output_path, &backup_path)?;

    let mut output = fs::File::create(&output_path)?;
    writeln!(output, "{preamble}\n")?;

    write!(output, "{kinds}")?;

    writeln!(output, "// Tokens\n\n")?;
    writeln!(output, "{tokens}")?;

    writeln!(output, "// Nodes\n\n")?;
    writeln!(output, "{nodes}")?;

    let Ok(output) = std::process::Command::new("rustfmt")
        .arg(&output_path)
        .output()
    else {
        fs::copy(&backup_path, &output_path)?;
        fs::remove_file(&backup_path)?;
        panic!("failed to run rustfmt")
    };

    if !output.status.success() {
        fs::copy(&backup_path, &output_path)?;
        fs::remove_file(&backup_path)?;
        panic!("{output:?}")
    }

    let Ok(post_check) = std::process::Command::new("cargo")
        .args(["check", "--color", "always", "-p", "mist-syntax"])
        .output()
    else {
        fs::copy(&backup_path, &output_path)?;
        fs::remove_file(&backup_path)?;
        panic!("failed to run cargo check")
    };

    if !post_check.status.success() {
        fs::copy(&backup_path, &output_path)?;
        fs::remove_file(&backup_path)?;
        panic!("{}", std::str::from_utf8(&post_check.stderr).unwrap())
    }

    fs::remove_file(&backup_path)?;

    Ok(())
}

fn generate_syntax_kinds(grammar: KindsSrc) -> String {
    let (single_byte_tokens_values, single_byte_tokens): (Vec<_>, Vec<_>) = grammar
        .punct
        .iter()
        .filter(|(token, _name)| token.len() == 1)
        .map(|(token, name)| (token.chars().next().unwrap(), format_ident!("{}", name)))
        .unzip();

    let punctuation_values = grammar.punct.iter().map(|(token, _name)| {
        if "{}[]()".contains(token) {
            let c = token.chars().next().unwrap();
            quote! { #c }
        } else {
            let cs = token.chars().map(|c| Punct::new(c, Spacing::Joint));
            quote! { #(#cs)* }
        }
    });
    let (punctuation_sk, punctuation_display, punctuation): (Vec<_>, Vec<_>, Vec<_>) = grammar
        .punct
        .iter()
        .map(|(token, name)| {
            let name = format_ident!("{}", name);
            (
                quote!(#[token(#token)] #name),
                quote!(#name => #token),
                name,
            )
        })
        .multiunzip();

    let x = |&name| match name {
        "Self" => format_ident!("SELF_TYPE_KW"),
        name => format_ident!("{}_KW", name.to_shouty_snake_case()),
    };
    let full_keywords_values = grammar.keywords;
    let full_keywords = full_keywords_values.iter().map(x);

    let contextual_keywords_values = &grammar.contextual_keywords;
    let contextual_keywords = contextual_keywords_values.iter().map(x);

    let all_keywords_values = grammar
        .keywords
        .iter()
        .chain(grammar.contextual_keywords.iter())
        .copied()
        .collect::<Vec<_>>();
    let all_keywords_idents = all_keywords_values.iter().map(|kw| format_ident!("{}", kw));
    let (all_keywords_sk, all_keywords): (Vec<_>, Vec<_>) = all_keywords_values
        .iter()
        .map(|kw| {
            let name = x(kw);
            (quote!(#[token(#kw)] #name), name)
        })
        .unzip();

    let (literals_sk, literals): (Vec<_>, Vec<_>) = grammar
        .literals
        .iter()
        .map(|name| {
            let tok = format_ident!("{}", name);
            match *name {
                "INT_NUMBER" => (quote!(#[regex(r"0|[1-9][0-9]*")] #tok), tok),
                _ => (quote!(#tok), tok),
            }
        })
        .unzip();

    let tokens = grammar
        .tokens
        .iter()
        .map(|name| {
            let tok = format_ident!("{}", name);
            match *name {
                "WHITESPACE" => quote!(#[regex(r"[ \t\n\f]+")] #tok),
                "IDENT" => quote!(#[regex(r"[a-zA-Z_][a-zA-Z_0-9]*")] #tok),
                "COMMENT" => quote!(#[regex(r"//.*\n")] #tok),
                _ => quote!(#tok),
            }
        })
        .collect::<Vec<_>>();

    let nodes = grammar
        .nodes
        .iter()
        .map(|name| format_ident!("{}", name))
        .collect::<Vec<_>>();

    let ast = quote! {
        /// The kind of syntax node, e.g. `IDENT`, `USE_KW`, or `STRUCT`.
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, logos::Logos)]
        #[repr(u16)]
        pub enum SyntaxKind {
            // Technical SyntaxKinds: they appear temporally during parsing,
            // but never end up in the final tree
            #[doc(hidden)]
            TOMBSTONE,
            #[doc(hidden)]
            EOF,
            /// Punctuation
            #(#punctuation_sk,)*
            /// Keywords
            #(#all_keywords_sk,)*
            /// Literals
            #(#literals_sk,)*
            /// Tokens
            #(#tokens,)*
            /// Nodes
            #(#nodes,)*

            // Technical kind so that we can cast from u16 safely
            #[doc(hidden)]
            __LAST,
        }
        use self::SyntaxKind::*;

        impl std::fmt::Display for SyntaxKind {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let s = match self {
                    #(#punctuation_display,)*
                    _ => return write!(f, "{self:?}")
                };
                write!(f, "{s}")
            }
        }

        impl SyntaxKind {
            pub fn is_keyword(self) -> bool {
                matches!(self, #(#all_keywords)|*)
            }

            pub fn is_punct(self) -> bool {
                matches!(self, #(#punctuation)|*)
            }

            pub fn is_literal(self) -> bool {
                matches!(self, #(#literals)|*)
            }

            pub fn from_keyword(ident: &str) -> Option<SyntaxKind> {
                let kw = match ident {
                    #(#full_keywords_values => #full_keywords,)*
                    _ => return None,
                };
                Some(kw)
            }

            pub fn from_contextual_keyword(ident: &str) -> Option<SyntaxKind> {
                let kw = match ident {
                    #(#contextual_keywords_values => #contextual_keywords,)*
                    _ => return None,
                };
                Some(kw)
            }

            pub fn from_char(c: char) -> Option<SyntaxKind> {
                let tok = match c {
                    #(#single_byte_tokens_values => #single_byte_tokens,)*
                    _ => return None,
                };
                Some(tok)
            }
        }

        #[macro_export]
        macro_rules! T {
            #([#punctuation_values] => { $crate::SyntaxKind::#punctuation };)*
            #([#all_keywords_idents] => { $crate::SyntaxKind::#all_keywords };)*
            [lifetime_ident] => { $crate::SyntaxKind::LIFETIME_IDENT };
            [ident] => { $crate::SyntaxKind::IDENT };
            [shebang] => { $crate::SyntaxKind::SHEBANG };
        }
        pub use T;
    };

    ast.to_string()
}

impl Field {
    pub(crate) fn method_name(&self) -> proc_macro2::Ident {
        match self {
            Field::Token(tok) => format_ident!("{}_token", name_symbol(tok).unwrap_or(tok)),
            Field::Node { name, .. } => {
                if name == "type" {
                    format_ident!("ty")
                } else {
                    format_ident!("{name}")
                }
            }
        }
    }

    fn is_many(&self) -> bool {
        matches!(
            self,
            Field::Node {
                cardinality: Cardinality::Many,
                ..
            }
        )
    }

    fn token_kind(&self) -> Option<proc_macro2::TokenStream> {
        match self {
            Field::Token(token) => {
                let token: proc_macro2::TokenStream = token.parse().unwrap();
                Some(quote! { T![#token] })
            }
            _ => None,
        }
    }

    fn ty(&self) -> proc_macro2::Ident {
        match self {
            Field::Token(_) => format_ident!("SyntaxToken"),
            Field::Node { ty, .. } => format_ident!("{}", ty),
        }
    }
}

fn generate_tokens(grammar: &AstSrc) -> String {
    let tokens = grammar.tokens.iter().map(|token| {
        let name = format_ident!("{}", token);
        let kind = format_ident!("{}", token.to_shouty_snake_case());
        quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub struct #name {
                pub(crate) syntax: SyntaxToken,
            }
            impl std::fmt::Display for #name {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    std::fmt::Display::fmt(&self.syntax, f)
                }
            }
            impl AstToken for #name {
                fn can_cast(kind: SyntaxKind) -> bool { kind == #kind }
                fn cast(syntax: SyntaxToken) -> Option<Self> {
                    if Self::can_cast(syntax.kind()) { Some(Self { syntax }) } else { None }
                }
                fn syntax(&self) -> &SyntaxToken { &self.syntax }
            }
        }
    });

    tokens.format("\n").to_string()
}

fn generate_nodes(grammar: &AstSrc) -> String {
    let nodes = grammar.nodes.iter().map(|node| {
        let name = format_ident!("{}", node.name);
        let kind = format_ident!("{}", node.name.to_shouty_snake_case());
        let traits = node.traits.iter().map(|trait_name| {
            let trait_name = format_ident!("{}", trait_name);
            quote!(impl crate::ast::#trait_name for #name {})
        });

        let methods = node.fields.iter().map(|field| {
            let method_name = field.method_name();
            let ty = field.ty();

            if field.is_many() {
                quote! {
                    pub fn #method_name(&self) -> AstChildren<#ty> {
                        support::children(&self.syntax)
                    }
                }
            } else if let Some(token_kind) = field.token_kind() {
                quote! {
                    pub fn #method_name(&self) -> Option<#ty> {
                        support::token(&self.syntax, #token_kind)
                    }
                }
            } else {
                quote! {
                    pub fn #method_name(&self) -> Option<#ty> {
                        support::child(&self.syntax)
                    }
                }
            }
        });

        quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub struct #name {
                pub(crate) syntax: SyntaxNode,
            }

            #(#traits)*

            impl #name {
                #(#methods)*
            }

            impl AstNode for #name {
                fn can_cast(kind: SyntaxKind) -> bool {
                    kind == #kind
                }
                fn cast(syntax: SyntaxNode) -> Option<Self> {
                    if Self::can_cast(syntax.kind()) { Some(Self { syntax }) } else { None }
                }
                fn syntax(&self) -> &SyntaxNode { &self.syntax }
            }
        }
    });

    let enums = grammar.enums.iter().map(|en| {
        let variants: Vec<_> = en
            .variants
            .iter()
            .map(|var| format_ident!("{}", var))
            .collect();
        let name = format_ident!("{}", en.name);
        let kinds: Vec<_> = variants
            .iter()
            .map(|name| format_ident!("{}", name.to_string().to_shouty_snake_case()))
            .collect();

        let ast_node = if en.name == "Stmt" {
            quote! {}
        } else {
            quote! {
                impl AstNode for #name {
                    fn can_cast(kind: SyntaxKind) -> bool {
                        matches!(kind, #(#kinds)|*)
                    }
                    fn cast(syntax: SyntaxNode) -> Option<Self> {
                        let res = match syntax.kind() {
                            #(
                            #kinds => #name::#variants(#variants { syntax }),
                            )*
                            _ => return None,
                        };
                        Some(res)
                    }
                    fn syntax(&self) -> &SyntaxNode {
                        match self {
                            #(
                            #name::#variants(it) => &it.syntax,
                            )*
                        }
                    }
                }
            }
        };

        quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub enum #name {
                #(#variants(#variants),)*
            }

            #(
                impl From<#variants> for #name {
                    fn from(node: #variants) -> #name {
                        #name::#variants(node)
                    }
                }
            )*

            #ast_node
        }
    });

    let enum_names = grammar.enums.iter().map(|it| &it.name);
    let node_names = grammar.nodes.iter().map(|it| &it.name);

    let display_impls = enum_names
        .chain(node_names.clone())
        .map(|it| format_ident!("{}", it))
        .map(|name| {
            quote! {
                impl std::fmt::Display for #name {
                    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                        std::fmt::Display::fmt(self.syntax(), f)
                    }
                }
            }
        });

    quote! {
        #(#nodes)*
        #(#enums)*
        #(#display_impls)*
    }
    .to_string()
}

fn lower(grammar: &Grammar) -> AstSrc {
    let mut res = AstSrc {
        tokens: "Whitespace Comment String ByteString IntNumber FloatNumber Char Byte Ident"
            .split_ascii_whitespace()
            .map(|it| it.to_string())
            .collect::<Vec<_>>(),
        ..Default::default()
    };

    let nodes = grammar.iter().collect::<Vec<_>>();

    for &node in &nodes {
        let name = grammar[node].name.clone();
        let rule = &grammar[node].rule;
        eprintln!("lowering {name:?}");
        match lower_enum(grammar, rule) {
            Some(variants) => {
                let enum_src = AstEnumSrc { name, variants };
                res.enums.push(enum_src);
            }
            None => {
                let mut fields = vec![];
                lower_rule(&mut fields, grammar, None, rule);
                res.nodes.push(AstNodeSrc {
                    name,
                    traits: Vec::new(),
                    fields,
                });
            }
        }
    }

    deduplicate_fields(&mut res);
    extract_enums(&mut res);
    extract_struct_traits(&mut res);

    res
}

fn deduplicate_fields(ast: &mut AstSrc) {
    for node in &mut ast.nodes {
        let mut i = 0;
        'outer: while i < node.fields.len() {
            for j in 0..i {
                let f1 = &node.fields[i];
                let f2 = &node.fields[j];
                if f1 == f2 {
                    node.fields.remove(i);
                    continue 'outer;
                }
            }
            i += 1;
        }
    }
}

fn extract_enums(ast: &mut AstSrc) {
    for node in &mut ast.nodes {
        for enm in &ast.enums {
            let mut to_remove = Vec::new();
            for (i, field) in node.fields.iter().enumerate() {
                let ty = field.ty().to_string();
                if enm.variants.iter().any(|it| it == &ty) {
                    to_remove.push(i);
                }
            }
            if to_remove.len() == enm.variants.len() {
                node.remove_field(to_remove);
                let ty = enm.name.clone();
                let name = ty.to_snake_case();
                node.fields.push(Field::Node {
                    name,
                    ty,
                    cardinality: Cardinality::Optional,
                });
            }
        }
    }
}

fn extract_struct_traits(ast: &mut AstSrc) {
    let traits: &[(&str, &[&str])] = &[
        ("HasAttrs", &["attrs"]),
        ("HasName", &["name"]),
        // ("HasVisibility", &["visibility"]),
        // ("HasGenericParams", &["generic_param_list", "where_clause"]),
        // ("HasTypeBounds", &["type_bound_list", "colon_token"]),
        // ("HasModuleItem", &["items"]),
        // ("HasLoopBody", &["label", "loop_body"]),
        // ("HasArgList", &["arg_list"]),
    ];

    for node in &mut ast.nodes {
        for (name, methods) in traits {
            extract_struct_trait(node, name, methods);
        }
    }

    let nodes_with_doc_comments = [
        // "SourceFile",
        // "Fn",
        // "Struct",
        // "Union",
        // "RecordField",
        // "TupleField",
        // "Enum",
        // "Variant",
        // "Trait",
        // "TraitAlias",
        // "Module",
        // "Static",
        // "Const",
        // "TypeAlias",
        // "Impl",
        // "ExternBlock",
        // "ExternCrate",
        // "MacroCall",
        // "MacroRules",
        // "MacroDef",
        // "Use",
    ];

    for node in &mut ast.nodes {
        if nodes_with_doc_comments.contains(&&*node.name) {
            node.traits.push("HasDocComments".into());
        }
    }
}

fn extract_struct_trait(node: &mut AstNodeSrc, trait_name: &str, methods: &&[&str]) {
    let mut to_remove = Vec::new();
    for (i, field) in node.fields.iter().enumerate() {
        let method_name = field.method_name().to_string();
        if methods.iter().any(|&it| it == method_name) {
            to_remove.push(i);
        }
    }
    if to_remove.len() == methods.len() {
        node.traits.push(trait_name.to_string());
        node.remove_field(to_remove);
    }
}

fn lower_enum(grammar: &Grammar, rule: &Rule) -> Option<Vec<String>> {
    let alternatives = match rule {
        Rule::Alt(it) => it,
        _ => return None,
    };
    let mut variants = vec![];
    for alternative in alternatives {
        match alternative {
            Rule::Node(it) => variants.push(grammar[*it].name.clone()),
            Rule::Token(it) if grammar[*it].name == ";" => (),
            r => {
                eprintln!("ehh {r:?}");
                return None;
            }
        }
    }
    Some(variants)
}

fn lower_rule(acc: &mut Vec<Field>, grammar: &Grammar, label: Option<&String>, rule: &Rule) {
    match rule {
        Rule::Labeled { label: l, rule } => {
            assert!(label.is_none());
            let manually_implemented = matches!(
                l.as_str(),
                "lhs"
                    | "rhs"
                    | "then_branch"
                    | "else_branch"
                    | "start"
                    | "end"
                    | "op"
                    | "index"
                    | "base"
                    | "value"
                    | "trait"
                    | "self_ty"
                    | "iterable"
                    | "condition"
            );
            if manually_implemented {
                return;
            }
            lower_rule(acc, grammar, Some(l), rule);
        }
        Rule::Node(node) => {
            let ty = grammar[*node].name.clone();
            let name = label.cloned().unwrap_or_else(|| ty.to_snake_case());
            let field = Field::Node {
                name,
                ty,
                cardinality: Cardinality::Optional,
            };
            acc.push(field);
        }
        Rule::Token(t) => {
            assert!(label.is_none(), "label was {label:?}");
            let mut name = grammar[*t].name.clone();
            if name != "int_number" && name != "string" {
                if "[]{}()".contains(&name) {
                    name = format!("'{name}'");
                }
                let field = Field::Token(name);
                acc.push(field);
            }
        }
        Rule::Seq(rules) | Rule::Alt(rules) => {
            for rule in rules {
                lower_rule(acc, grammar, label, rule);
            }
        }
        Rule::Opt(rule) => lower_rule(acc, grammar, label, rule),
        Rule::Rep(inner) => {
            if let Rule::Node(node) = &**inner {
                let ty = grammar[*node].name.clone();
                let name = label.cloned().unwrap_or_else(|| ty.to_snake_case() + "s");
                let field = Field::Node {
                    name,
                    ty,
                    cardinality: Cardinality::Many,
                };
                acc.push(field);
                return;
            }
            panic!("unhandled  rule: {rule:?}")
        }
    }
}

fn name_symbol(name: &str) -> Option<&str> {
    Some(match name {
        ";" => "semicolon",
        "->" => "thin_arrow",
        "'{'" => "l_curly",
        "'}'" => "r_curly",
        "'('" => "l_paren",
        "')'" => "r_paren",
        "'['" => "l_brack",
        "']'" => "r_brack",
        "<" => "l_angle",
        ">" => "r_angle",
        "=" => "eq",
        "!" => "excl",
        "*" => "star",
        "&" => "amp",
        "_" => "underscore",
        "." => "dot",
        ".." => "dotdot",
        "..." => "dotdotdot",
        "..=" => "dotdoteq",
        "=>" => "fat_arrow",
        "@" => "at",
        ":" => "colon",
        "::" => "coloncolon",
        "#" => "pound",
        "?" => "question_mark",
        "," => "comma",
        "|" => "pipe",
        "~" => "tilde",
        _ => return None,
    })
}
