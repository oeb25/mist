use std::{collections::HashMap, fmt::Write};

use derive_new::new;
use la_arena::{Arena, ArenaMap};
use mist_core::{
    hir::{self, ExprIdx, Item, ItemContext},
    mir,
};
use mist_syntax::SourceSpan;
use silvers::{
    expression::{AbstractLocalVar, Exp, LocationAccess, QuantifierExp, ResourceAccess, SeqExp},
    program::{Function, LocalVarDecl},
    typ::Type,
};

use crate::lower::{pure, ViperBody, ViperLowerError};

#[salsa::tracked]
pub fn viper_file(db: &dyn crate::Db, program: hir::Program) -> silvers::program::Program<VExprId> {
    let mut fields = vec![];
    let mut predicates = vec![];
    let mut methods = vec![];
    let mut functions = vec![];

    for item in program.items(db) {
        let Some(item) = hir::item(db, program, item.clone()) else { continue };
        match item {
            hir::Item::Type(ty_decl) => match ty_decl.data(db) {
                hir::TypeDeclData::Struct(s) => {}
            },
            hir::Item::TypeInvariant(_) => {}
            hir::Item::Function(function) => {
                if let Some((cx, source_map)) = hir::item_lower(db, program, item) {
                    // let (mir, mir_source_map) = mir::lower_item(db, cx);
                    // let mut lower = pure::PureLower::new(&cx, &mir);
                    // match  pure::lower_body_purest(db, program, &cx, &mir) {
                    //     Some(Ok((exp, arena, viper_source_map))) => {}
                    //     Some(err) => {}
                    //     None => {}
                    // }
                    // let mut lower_expr_pure = |e| match lower.lower_expr_pure(true, e) {
                    //     Ok(expr) => {
                    //         let mut writer = ViperWriter::new(&lower.arena);
                    //         writer.emit(&expr);
                    //         let output = writer.finish();
                    //         ViperHints::push(
                    //             db,
                    //             ViperHint::new(source_map.expr_span(e), output.buf),
                    //         );
                    //     }
                    //     Err(err) => {
                    //         ViperLowerErrors::push(db, err.spanned(&source_map));
                    //     }
                    // };

                    // for cond in cx.conditions() {
                    //     for expr in cond.exprs() {
                    //         lower_expr_pure(*expr);
                    //     }
                    // }
                    // if let Some(body) = cx.body_expr() {
                    //     lower_expr_pure(body);
                    // }
                }
            }
        }
    }

    silvers::program::Program {
        domains: vec![],
        fields,
        functions,
        predicates,
        methods,
        extensions: vec![],
    }
}

pub fn viper_item(
    db: &dyn crate::Db,
    cx: ItemContext,
    item: Item,
    mir: &mir::Body,
) -> Result<Option<ViperOutput>, ViperLowerError> {
    match item {
        hir::Item::Type(ty_decl) => match ty_decl.data(db) {
            hir::TypeDeclData::Struct(s) => Ok(None),
        },
        hir::Item::TypeInvariant(_) => Ok(None),
        hir::Item::Function(function) => {
            let mut lower = pure::PureLower::new(&cx, &mir);

            let formal_args = vec![];
            // let formal_args = cx
            //     .params()
            //     .iter()
            //     .map(|param| {
            //         Ok(LocalVarDecl {
            //             name: cx.var_ident(param.name).to_string(),
            //             typ: lower.lower_ty(param.ty)?,
            //         })
            //     })
            //     .collect::<Result<_, _>>()?;

            let mut pres = vec![];
            let mut posts = vec![];

            for &pre in mir.requires() {
                pres.push(lower.lower(pre)?);
            }
            for &post in mir.ensures() {
                posts.push(lower.lower(post)?);
            }
            for &inv in mir.invariants() {
                let exp = lower.lower(inv)?;
                pres.push(exp);
                posts.push(exp);
            }

            let Some(ret_ty) = function.ret(db) else { return Ok(None) };

            let func = silvers::program::Function {
                name: function.name(db).to_string(),
                formal_args,
                // typ: lower.lower_ty(ret_ty)?,
                typ: Type::internal_type(),
                pres,
                posts,
                body: mir.body_block().map(|body| lower.lower(body)).transpose()?,
            };

            let (viper_body, viper_source_map) = lower.finish();

            let mut writer = ViperWriter::new(&viper_body);
            writer.emit(&func);
            Ok(Some(writer.finish()))
        }
    }
}

#[derive(new, Debug, Clone)]
pub struct ViperHint {
    pub span: SourceSpan,
    pub viper: String,
}

#[salsa::accumulator]
pub struct ViperHints(ViperHint);

#[derive(Default)]
pub struct ViperSourceMap {
    pub(crate) expr_map: HashMap<ExprIdx, VExprId>,
    pub(crate) expr_map_back: HashMap<VExprId, ExprIdx>,
}

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
type VExprData = Exp<VExprId>;

pub type VExprId = la_arena::Idx<VExpr>;
#[derive(new, Debug, Clone, PartialEq, Eq, Hash, derive_more::Deref)]
pub struct VExpr {
    data: VExprData,
}

#[derive(new)]
pub(crate) struct ViperWriter<'a> {
    body: &'a ViperBody,
    #[new(default)]
    start_of_line: bool,
    #[new(default)]
    indentation: usize,
    #[new(default)]
    output: ViperOutput,
}

#[derive(Debug, Default)]
pub struct ViperOutput {
    pub buf: String,
    pub expr_map: ArenaMap<VExprId, SourceSpan>,
    pub expr_map_back: HashMap<SourceSpan, VExprId>,
}

impl ViperWriter<'_> {
    pub(crate) fn finish(self) -> ViperOutput {
        self.output
    }
    pub(crate) fn emit<E: ViperWrite>(&mut self, elem: &E) {
        let start = self.output.buf.len();

        E::emit(elem, self);

        let end = self.output.buf.len();
        let span = SourceSpan::new_start_end(start, end);

        E::register(elem, self, span);
    }

    fn indent(&mut self, f: impl FnOnce(&mut Self)) {
        self.indentation += 2;
        f(self);
        self.indentation -= 2;
    }
}

pub(crate) trait ViperWrite {
    fn emit(elem: &Self, writer: &mut ViperWriter);
    fn register(elem: &Self, writer: &mut ViperWriter, span: SourceSpan) {
        let _ = (elem, writer, span);
    }
}

mod write_impl {
    use super::*;

    macro_rules! indentation_pre {
        ($w:expr) => {
            if $w.start_of_line {
                for _ in 0..$w.indentation {
                    write!($w.output.buf, " ").unwrap();
                }
            }
            $w.start_of_line = false;
        };
    }
    macro_rules! w {
        ($w:expr, $str:literal) => {{
            indentation_pre!($w);
            write!($w.output.buf, $str).unwrap();
        }};
        ($w:expr, $e:expr) => {{
            indentation_pre!($w);
            $w.emit($e);
        }};
        ($w:expr, $str:literal, $($t:tt)*) => {{
            indentation_pre!($w);
            write!($w.output.buf, $str).unwrap();
            w!($w, $($t)*);
        }};
        ($w:expr, $e:expr, $($t:tt)*) => {{
            indentation_pre!($w);
            $w.emit($e);
            w!($w, $($t)*);
        }};
    }
    macro_rules! wln {
        () => {};
        ($w:expr, $str:literal) => {{
            indentation_pre!($w);
            writeln!($w.output.buf, $str).unwrap();
            $w.start_of_line = true;
        }};
        ($w:expr, $e:expr) => {{
            indentation_pre!($w);
            $w.emit($e);
            writeln!($w.output.buf).unwrap();
            $w.start_of_line = true;
        }};
        ($w:expr, $str:literal, $($t:tt)*) => {{
            indentation_pre!($w);
            write!($w.output.buf, $str).unwrap();
            wln!($w, $($t)*);
        }};
        ($w:expr, $e:expr, $($t:tt)*) => {{
            indentation_pre!($w);
            $w.emit($e);
            wln!($w, $($t)*);
        }};
    }

    impl ViperWrite for VExprId {
        fn emit(&vexpr: &Self, w: &mut ViperWriter) {
            match &w.body[vexpr].data {
                Exp::Bin { op, left, right } => w!(w, "(", left, " {op} ", right, ")"),
                Exp::Un { op, exp } => w!(w, "{op}", exp),
                Exp::MagicWand(m) => w!(w, "(", &m.left, " --* ", &m.right, ")"),
                Exp::Literal(l) => w!(w, "{l}"),
                Exp::AccessPredicate(_) => todo!(),
                Exp::Perm(_) => todo!(),
                Exp::FuncApp { funcname, args } => {
                    w!(w, "{funcname}(");
                    let mut first = true;
                    for arg in args {
                        if !first {
                            w!(w, ", ");
                        }
                        first = false;
                        w!(w, arg);
                    }
                    w!(w, ")");
                }
                Exp::DomainFuncApp {
                    funcname,
                    args,
                    typ_var_map,
                } => todo!(),
                Exp::BackendFuncApp {
                    backend_func_name,
                    args,
                } => todo!(),
                Exp::LocationAccess(r) => match r {
                    ResourceAccess::Location(l) => match l {
                        LocationAccess::Field(f) => {
                            let name = &f.field;
                            w!(w, &f.rcr, ".{name}")
                        }
                        LocationAccess::Predicate(_) => todo!(),
                    },
                },
                Exp::Cond { cond, thn, els } => {
                    wln!(w, "(", cond);
                    w.indent(|w| {
                        w!(w, "? ");
                        w.indent(|w| wln!(w, thn));
                        w!(w, ": ");
                        w.indent(|w| w!(w, els, ")"));
                        // w!(w, ": ", els, ")");
                    })
                }
                Exp::Unfolding { acc, body } => todo!(),
                Exp::Applying { wand, body } => todo!(),
                Exp::Old(_) => todo!(),
                Exp::Let {
                    variable,
                    exp,
                    body,
                } => {
                    let name = &variable.name;
                    w!(w, "(let {name} == (");
                    w.indent(|w| wln!(w, exp, ") in"));
                    w!(w, body, ")");
                    // w.indent(|w| w!(w, body, ")"));
                }
                Exp::Quantifier(
                    q @ QuantifierExp::Exists {
                        variables,
                        triggers,
                        exp,
                    }
                    | q @ QuantifierExp::Forall {
                        variables,
                        triggers,
                        exp,
                    },
                ) => {
                    let q = match q {
                        QuantifierExp::Forall { .. } => "forall",
                        QuantifierExp::Exists { .. } => "exists",
                        QuantifierExp::ForPerm { .. } => unreachable!(),
                    };
                    w!(w, "({q} ");
                    let mut first = true;
                    for var in variables {
                        if !first {
                            w!(w, ", ");
                        }
                        first = false;
                        let name = &var.name;
                        let ty = &var.typ;
                        w!(w, "{name}: ", ty)
                    }
                    w!(w, " :: ", exp, ")");
                }
                Exp::Quantifier(QuantifierExp::ForPerm {
                    variables,
                    resource,
                    exp,
                }) => todo!(),
                Exp::AbstractLocalVar(v) => match v {
                    AbstractLocalVar::LocalVar(l) => {
                        let name = &l.name;
                        w!(w, "{name}")
                    }
                    AbstractLocalVar::Result { typ } => w!(w, "result"),
                },
                Exp::Seq(s) => match s {
                    SeqExp::Empty { elem_typ } => w!(w, "Seq[", elem_typ, "]()"),
                    SeqExp::Explicit { elems } => {
                        w!(w, "Seq(");
                        let mut first = true;
                        for e in elems {
                            if !first {
                                w!(w, ", ");
                            }
                            first = false;
                            w!(w, e);
                        }
                        w!(w, ")");
                    }
                    SeqExp::Range { low, high } => todo!(),
                    SeqExp::Append { left, right } => todo!(),
                    SeqExp::Index { s, idx } => w!(w, s, "[", idx, "]"),
                    SeqExp::Take { s, n } => w!(w, s, "[", "..", n, "]"),
                    SeqExp::Drop { s, n } => w!(w, s, "[", n, "..", "]"),
                    SeqExp::Contains { elem, s } => todo!(),
                    SeqExp::Update { s, idx, elem } => todo!(),
                    SeqExp::Length { s } => w!(w, "|", s, "|"),
                },
                Exp::Set(_) => todo!(),
                Exp::Multiset(_) => todo!(),
                Exp::Map(_) => todo!(),
            }
        }

        fn register<'a>(&vexpr: &Self, writer: &mut ViperWriter<'a>, span: SourceSpan) {
            writer.output.expr_map.insert(vexpr, span);
            writer.output.expr_map_back.insert(span, vexpr);
        }
    }

    impl ViperWrite for Type {
        fn emit(elem: &Self, w: &mut ViperWriter) {
            w!(w, "{elem}");
        }
    }

    impl<E: ViperWrite> ViperWrite for Function<E> {
        fn emit(elem: &Self, w: &mut ViperWriter) {
            let name = &elem.name;
            wln!(w, "function {name}(): ", &elem.typ);
            w.indent(|w| {
                for e in &elem.pres {
                    wln!(w, "requires");
                    w.indent(|w| wln!(w, e));
                }
                for e in &elem.posts {
                    wln!(w, "ensures");
                    w.indent(|w| wln!(w, e));
                }
            });
            if let Some(b) = &elem.body {
                wln!(w, "{{");
                w.indent(|w| {
                    wln!(w, b);
                });
                wln!(w, "}}");
            }
        }
    }

    /*
    #[derive(Debug, Clone, PartialEq, Eq, Hash, Display)]
    #[display(bound = "E: std::fmt::Display")]
    #[display(
        fmt = "function {name}({}): {typ}\n{}\n{}{}",
        "comma(formal_args)",
        "indented(prefixed(\"requires \", pres))",
        "indented(prefixed(\"ensures  \", posts))",
        "opt_body(body)"
    )]
    pub struct Function<E> {
        pub name: String,
        pub formal_args: Vec<LocalVarDecl>,
        pub typ: Type,
        pub pres: Vec<E>,
        pub posts: Vec<E>,
        pub body: Option<E>,
    }
    */
}
