use std::{fs, io::Write, path::PathBuf};

use itertools::Itertools;
use miette::{miette, Diagnostic, IntoDiagnostic, Result};
use mist_core::util::Position;
use mist_syntax::SourceSpan;
use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote};
use ungrammar::{Grammar, Node, Rule};

#[test]
fn sourcegen_wasm() -> Result<()> {
    miette::set_panic_hook();

    let grammar_src = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/src/wasm/wasm.ungram"));
    let grammar: Grammar =
        grammar_src.parse().map_err(|err| ungrammar_to_miette(grammar_src, err))?;

    let adts = generate_adts(&grammar);

    let mut rustfmt = std::process::Command::new("rustfmt")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .into_diagnostic()?;

    writeln!(rustfmt.stdin.take().unwrap(), "{adts}").into_diagnostic()?;
    let code = String::from_utf8(rustfmt.wait_with_output().into_diagnostic()?.stdout).unwrap();

    let output_path = PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/src/wasm/ast.rs"));
    let mut output = fs::File::create(output_path).into_diagnostic()?;
    writeln!(output, "{code}").into_diagnostic()?;

    Ok(())
}

fn generate_adts(grammar: &Grammar) -> String {
    grammar.iter().map(|node| generate_adt(grammar, node)).join("\n\n")
}
fn generate_adt(grammar: &Grammar, node: Node) -> TokenStream {
    let name = format_ident!("{}", grammar[node].name);

    match pre_rule(grammar, &grammar[node].rule) {
        IRule::Internal(internal) => match internal {
            Internal::U32 => quote!(),
            Internal::Id => quote!(
                #[derive(Debug, Clone, PartialEq, Eq, Hash)]
                pub struct Id(pub String);
            ),
            Internal::Name => quote!(
                #[derive(Debug, Clone, PartialEq, Eq, Hash)]
                pub struct Name(pub String);
            ),
            Internal::ValType => quote!(
                #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
                #[non_exhaustive]
                pub enum ValType {
                    I32,
                    I64,
                    F32,
                    F64,
                    V128,
                    Funcref,
                    Externref,
                }
            ),
            Internal::Instr => {
                let (instrs, names, idxs): (Vec<_>, Vec<_>, Vec<_>) = INSTRS
                    .iter()
                    .map(|(name, idx)| {
                        let pname = format_ident!("{}", heck::AsPascalCase(*name).to_string());
                        (pname, *name, *idx)
                    })
                    .multiunzip();
                quote!(
                    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
                    pub struct Instr {
                        pub kind: InstrKind,
                        pub args: Vec<()>,
                    }
                    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
                    pub enum InstrKind {
                        #(#instrs),*
                    }
                    impl  InstrKind {
                        pub fn instr_id(&self) -> u32 {
                            match self {
                                #(Self::#instrs => #idxs),*
                            }
                        }
                    }
                    impl std::fmt::Display for InstrKind {
                        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                            match self {
                                #(Self::#instrs => write!(f, #names),)*
                            }
                        }
                    }
                )
            }
        },
        IRule::Rule(r) => match r {
            Rule::Labeled { label, rule } => {
                let (ty, _inner_name) = generate_adt_inner(grammar, rule).unwrap();
                let label = format_ident!("{label}");
                quote! {
                    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
                    pub struct #name { pub #label:#ty }
                }
            }
            Rule::Node(_) => {
                let (ty, _inner_name) = generate_adt_inner(grammar, &grammar[node].rule).unwrap();
                quote! {
                #[derive(Debug, Clone, PartialEq, Eq, Hash)]
                pub struct #name(#ty);}
            }
            Rule::Alt(options) => {
                let options = options
                    .iter()
                    .map(|o| {
                        let (ty, name) =
                            generate_adt_inner(grammar, o).unwrap_or_else(|| match o {
                                Rule::Token(tok) => {
                                    let t = &grammar[*tok].name;
                                    (quote!(#t), None)
                                }
                                _ => panic!(),
                            });
                        let name = name.map(|name| {
                            format_ident!("{}", heck::AsPascalCase(name.to_string()).to_string())
                        });
                        quote!(#name(#ty))
                    })
                    .collect_vec();
                quote! {
                    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
                    pub enum #name { #(#options,)* }
                }
            }
            Rule::Token(_) => {
                quote! {
                    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
                    pub struct #name;
                }
            }
            Rule::Seq(rules) => {
                let fields = rules
                    .iter()
                    .filter_map(|r| match pre_rule(grammar, r) {
                        IRule::Internal(_) => {
                            let (ty, name) = generate_adt_inner(grammar, r).unwrap();
                            Some(quote!(#name: #ty))
                        }
                        IRule::Rule(Rule::Labeled { label, rule }) => {
                            let name = format_ident!("{label}");
                            let (ty, _) = generate_adt_inner(grammar, rule).unwrap();
                            Some(quote!(#name: #ty))
                        }
                        IRule::Rule(Rule::Node(_)) => {
                            let (ty, name) = generate_adt_inner(grammar, r).unwrap();
                            Some(quote!(#name: #ty))
                        }
                        IRule::Rule(Rule::Token(_)) => None,
                        IRule::Rule(Rule::Seq(_)) => todo!(),
                        IRule::Rule(Rule::Alt(_)) => todo!(),
                        IRule::Rule(Rule::Opt(inner)) => {
                            let (ty, name) = generate_adt_inner(grammar, inner)?;
                            Some(quote!(#name: Option<#ty>))
                        }
                        IRule::Rule(Rule::Rep(_)) => {
                            let (ty, name) = generate_adt_inner(grammar, r).unwrap();
                            Some(quote!(#name: #ty))
                        }
                    })
                    .collect_vec();

                quote! {
                    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
                    pub struct #name { #(pub #fields,)* }
                }
            }
            Rule::Opt(_) => todo!(),
            Rule::Rep(inner) => {
                let (inner, _) = generate_adt_inner(grammar, inner).unwrap();
                quote! {
                    #[derive(Debug, Clone, PartialEq, Eq, Hash)]
                    pub struct #name(pub Vec<#inner>);
                }
            }
        },
    }
}
fn generate_adt_inner(grammar: &Grammar, rule: &Rule) -> Option<(TokenStream, Option<Ident>)> {
    match pre_rule(grammar, rule) {
        IRule::Internal(internal) => match internal {
            Internal::U32 => Some((quote!(u32), Some(format_ident!("_u32")))),
            Internal::Id => Some((quote!(String), Some(format_ident!("id")))),
            Internal::Name => Some((quote!(String), Some(format_ident!("name")))),
            Internal::ValType => Some((quote!(()), Some(format_ident!("val_type")))),
            Internal::Instr => Some((quote!(Instr), Some(format_ident!("instr")))),
        },
        IRule::Rule(Rule::Labeled { label, rule }) => {
            Some((generate_adt_inner(grammar, rule)?.0, Some(format_ident!("{label}"))))
        }
        IRule::Rule(Rule::Node(n)) => {
            let raw_name = &grammar[*n].name;
            let name = format_ident!("{}", raw_name);
            let display_name = format_ident!("{}", heck::AsSnakeCase(raw_name).to_string());
            Some((quote!(#name), Some(display_name)))
        }
        IRule::Rule(Rule::Token(_)) => None,
        IRule::Rule(Rule::Seq(xs)) => {
            let xs = xs.iter().filter_map(|x| Some(generate_adt_inner(grammar, x)?.0));
            Some((quote!((#(#xs),*)), None))
        }
        IRule::Rule(Rule::Alt(_)) => todo!(),
        IRule::Rule(Rule::Opt(inner)) => {
            let (ty, name) = generate_adt_inner(grammar, inner)?;
            Some((quote!(Option<#ty>), name))
        }
        IRule::Rule(Rule::Rep(inner)) => {
            let (ty, name) = generate_adt_inner(grammar, inner)?;
            let name = name.map(|x| format_ident!("{x}s"));
            Some((quote!(Vec<#ty>), name))
        }
    }
}

enum IRule<'a> {
    Rule(&'a Rule),
    Internal(Internal),
}

enum Internal {
    U32,
    Id,
    Name,
    ValType,
    Instr,
}

fn pre_rule<'a>(grammar: &Grammar, rule: &'a Rule) -> IRule<'a> {
    match rule {
        Rule::Token(t) => match grammar[*t].name.as_str() {
            "u32" => IRule::Internal(Internal::U32),
            "id" => IRule::Internal(Internal::Id),
            "name" => IRule::Internal(Internal::Name),
            "valtype" => IRule::Internal(Internal::ValType),
            "instr" => IRule::Internal(Internal::Instr),
            _ => IRule::Rule(rule),
        },
        Rule::Seq(xs) => {
            let mut opts = xs.iter().filter(|r| !matches!(r, Rule::Token(_)));

            match (opts.next(), opts.next()) {
                (Some(r), None) => {
                    if rule == r {
                        todo!("{r:?}")
                    } else {
                        pre_rule(grammar, r)
                    }
                }
                _ => IRule::Rule(rule),
            }
        }
        Rule::Labeled { .. } | Rule::Node(_) | Rule::Alt(_) | Rule::Opt(_) | Rule::Rep(_) => {
            IRule::Rule(rule)
        }
    }
}

const INSTRS: [(&str, u32); 189] = [
    ("unreachable", 0),
    ("nop", 1),
    ("block", 2),
    ("loop", 3),
    ("if", 4),
    ("else", 5),
    ("end", 11),
    ("br", 12),
    ("br if", 13),
    ("br table", 14),
    ("return", 15),
    ("call", 16),
    ("call_indirect", 17),
    ("return_call", 18),
    ("return_call_indirect", 19),
    ("drop", 26),
    ("select", 27),
    ("select t", 28),
    ("get_local", 32),
    ("set_local", 33),
    ("tee_local", 34),
    ("get_global", 35),
    ("set_global", 36),
    ("table.get", 37),
    ("table.set", 38),
    ("i32.load", 40),
    ("i64.load", 41),
    ("f32.load", 42),
    ("f64.load", 43),
    ("i32.load8_s", 44),
    ("i32.load8_u", 45),
    ("i32.load16_s", 46),
    ("i32.load16_u", 47),
    ("i64.load8_s", 48),
    ("i64.load8_u", 49),
    ("i64.load16_s", 50),
    ("i64.load16_u", 51),
    ("i32.load32_s", 52),
    ("i32.load32_u", 53),
    ("i32.store", 54),
    ("i64.store", 55),
    ("f32.store", 56),
    ("f64.store", 57),
    ("i32.store8", 58),
    ("i32.store16", 59),
    ("i64.store8", 60),
    ("i64.sotre16", 61),
    ("i64.store32", 62),
    ("memory.size", 63),
    ("memory.grow", 64),
    ("i32.const", 65),
    ("i64.const", 66),
    ("f32.const", 67),
    ("f64.const", 68),
    ("i32.eqz", 69),
    ("i32.eq", 70),
    ("i32.ne", 71),
    ("i32.lt_s", 72),
    ("i32.lt_u", 73),
    ("i32.gt_s", 74),
    ("i32.gt_u", 75),
    ("i32.le_s", 76),
    ("i32.le_u", 77),
    ("i32.ge_s", 78),
    ("i32.ge_u", 79),
    ("i64.eqz", 80),
    ("i64.eq", 81),
    ("i64.ne", 82),
    ("i64.lt_s", 83),
    ("i64.lt_u", 84),
    ("i64.gt_s", 85),
    ("i64.gt_u", 86),
    ("i64.le_s", 87),
    ("i64.le_u", 88),
    ("i64.ge_s", 89),
    ("i64.ge_u", 90),
    ("f32.eq", 91),
    ("f32.ne", 92),
    ("f32.lt", 93),
    ("f32.gt", 94),
    ("f32.le", 95),
    ("f32.ge", 96),
    ("f64.eq", 97),
    ("f64.ne", 98),
    ("f64.lt", 99),
    ("f64.gt", 100),
    ("f64.le", 101),
    ("f64.ge", 102),
    ("i32.clz", 103),
    ("i32.ctz", 104),
    ("i32.popcnt", 105),
    ("i32.add", 106),
    ("i32.sub", 107),
    ("i32.mul", 108),
    ("i32.div_s", 109),
    ("i32.div_u", 110),
    ("i32.rem_s", 111),
    ("i32.rem_u", 112),
    ("i32.and", 113),
    ("i32.or", 114),
    ("i32.xor", 115),
    ("i32.shl", 116),
    ("i32.shr_s", 117),
    ("i32.shr_u", 118),
    ("i32.rotl", 119),
    ("i32.rotr", 120),
    ("i64.clz", 121),
    ("i64.ctz", 122),
    ("i64.popcnt", 123),
    ("i64.add", 124),
    ("i64.sub", 125),
    ("i64.mul", 126),
    ("i64.div_s", 127),
    ("i64.div_u", 128),
    ("i64.rem_s", 129),
    ("i64.rem_u", 130),
    ("i64.and", 131),
    ("i64.or", 132),
    ("i64.xor", 133),
    ("i64.shl", 134),
    ("i64.shr_s", 135),
    ("i64.shr_u", 136),
    ("i64.rotl", 137),
    ("i64.rotr", 138),
    ("f32.abs", 139),
    ("f32.neg", 140),
    ("f32.ceil", 141),
    ("f32.floor", 142),
    ("f32.trunc", 143),
    ("f32.nearest", 144),
    ("f32.sqrt", 145),
    ("f32.add", 146),
    ("f32.sub", 147),
    ("f32.mul", 148),
    ("f32.div", 149),
    ("f32.min", 150),
    ("f32.max", 151),
    ("f32.copysign", 152),
    ("f64.abs", 153),
    ("f64.neg", 154),
    ("f64.ceil", 155),
    ("f64.floor", 156),
    ("f64.trunc", 157),
    ("f64.nearest", 158),
    ("f64.sqrt", 159),
    ("f64.add", 160),
    ("f64.sub", 161),
    ("f64.mul", 162),
    ("f64.div", 163),
    ("f64.min", 164),
    ("f64.max", 165),
    ("f64.copysign", 166),
    ("i32.wrap/i64", 167),
    ("i32.trunc_s/f32", 168),
    ("i32.trunc_u/f32", 169),
    ("i32.trunc_s/f64", 170),
    ("i32.trunc_u/f64", 171),
    ("i64.extend_s/i32", 172),
    ("i64.extend_u/i32", 173),
    ("i64.trunc_s/f32", 174),
    ("i64.trunc_u/f32", 175),
    ("i64.trunc_s/f64", 176),
    ("i64.trunc_u/f64", 177),
    ("f32.convert_s/i32", 178),
    ("f32.convert_u/i32", 179),
    ("f32.convert_s/i64", 180),
    ("f32.convert_u/i64", 181),
    ("f32.demote/f64", 182),
    ("f64.convert_s/i32", 183),
    ("f64.convert_u/i32", 184),
    ("f64.convert_s/i64", 185),
    ("f64.convert_u/i64", 186),
    ("f64.promote/f32", 187),
    ("i32.reinterpret/f32", 188),
    ("i64.reinterpret/f64", 189),
    ("f32.reinterpret/i32", 190),
    ("f64.reinterpret/i64", 191),
    ("i32.extend8_s", 192),
    ("i32.extend16_s", 193),
    ("i64.extend8_s", 194),
    ("i64.extend16_s", 195),
    ("i64.extend32_s", 196),
    ("ref.null", 208),
    ("ref.is_null", 209),
    ("ref.func", 210),
    ("block with blocktype", 211),
    ("loop with blocktype", 212),
    ("if with blocktype", 213),
    ("debug break point", 214),
];

fn ungrammar_to_miette(src: &str, err: ungrammar::Error) -> miette::Error {
    let err = err.to_string();

    #[derive(thiserror::Error, Debug, Diagnostic)]
    #[error("ungrammar error: {raw}")]
    struct UngrammarMiette {
        #[source_code]
        src: String,
        raw: String,
        #[label("{msg}")]
        loc: SourceSpan,
        msg: String,
    }

    if let Some((loc, msg)) = err.split_once(": ") {
        let (row, col) = loc.split_once(':').unwrap();
        let [row, col] = [row, col].map(|x| x.parse::<u32>().unwrap());

        let pos = Position::new(row - 1, col - 1);
        let offset = pos.to_byte_offset(src).unwrap();

        UngrammarMiette {
            src: src.to_string(),
            raw: err.to_string(),
            loc: (offset, 0).into(),
            msg: msg.to_string(),
        }
        .into()
    } else {
        miette!("{}", err)
    }
}
