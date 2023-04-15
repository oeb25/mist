use std::{collections::HashMap, fmt::Write};

use derive_new::new;
use la_arena::Arena;
use mist_core::hir::{self, ExprIdx, Item, ItemContext};
use mist_syntax::SourceSpan;
use silvers::{
    expression::{AbstractLocalVar, Exp, LocationAccess, QuantifierExp, ResourceAccess, SeqExp},
    program::LocalVarDecl,
    typ::Type,
};
use tracing::debug;

use crate::lower::{ViperLower, ViperLowerError, ViperLowerErrors};

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
                    let mut lower = ViperLower::new(db, &cx);
                    let mut lower_expr_pure = |e| match lower.lower_expr_pure(true, e) {
                        Ok(expr) => {
                            let mut writer = ViperWriter::new(&lower.arena);
                            writer.emit(&expr);
                            let output = writer.finish();
                            ViperHints::push(
                                db,
                                ViperHint::new(source_map.expr_span(e), output.buf),
                            );
                        }
                        Err(err) => {
                            ViperLowerErrors::push(db, err.spanned(&source_map));
                        }
                    };

                    for cond in cx.conditions() {
                        for expr in cond.exprs() {
                            lower_expr_pure(*expr);
                        }
                    }
                    if let Some(body) = cx.body_expr() {
                        lower_expr_pure(body);
                    }
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
) -> Result<Option<ViperOutput>, ViperLowerError> {
    match item {
        hir::Item::Type(ty_decl) => match ty_decl.data(db) {
            hir::TypeDeclData::Struct(s) => Ok(None),
        },
        hir::Item::TypeInvariant(_) => Ok(None),
        hir::Item::Function(function) => {
            let mut lower = ViperLower::new(db, &cx);

            let formal_args = cx
                .params()
                .iter()
                .map(|param| {
                    Ok(LocalVarDecl {
                        name: cx.var_ident(param.name).to_string(),
                        typ: lower.lower_ty(param.ty)?,
                    })
                })
                .collect::<Result<_, _>>()?;

            let mut pres = vec![];
            let mut posts = vec![];

            for cond in cx.conditions() {
                let target = match cond {
                    hir::Condition::Requires(_) => &mut pres,
                    hir::Condition::Ensures(_) => &mut posts,
                };
                for expr in cond.exprs() {
                    target.push(lower.lower_expr_pure(true, *expr)?);
                }
            }

            let Some(ret_ty) = function.ret(db) else { return Ok(None) };

            silvers::program::Function {
                name: function.name(db).to_string(),
                formal_args,
                typ: lower.lower_ty(ret_ty)?,
                pres,
                posts,
                body: cx
                    .body_expr()
                    .map(|body| lower.lower_expr_pure(true, body))
                    .transpose()?,
            };

            todo!()
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
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct VExpr {
    data: VExprData,
}

#[derive(new)]
pub(crate) struct ViperWriter<'a> {
    arena: &'a Arena<VExpr>,
    #[new(default)]
    indentation: usize,
    #[new(default)]
    output: ViperOutput,
}

#[derive(Debug, Default)]
pub struct ViperOutput {
    pub(crate) buf: String,
    pub(crate) expr_map: HashMap<VExprId, SourceSpan>,
    pub(crate) expr_map_back: HashMap<SourceSpan, VExprId>,
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
}

pub(crate) trait ViperWrite {
    fn emit<'a>(elem: &Self, writer: &mut ViperWriter<'a>);
    fn register<'a>(elem: &Self, writer: &mut ViperWriter<'a>, span: SourceSpan) {
        let _ = (elem, writer, span);
    }
}

impl ViperWrite for VExprId {
    fn emit<'a>(&vexpr: &Self, writer: &mut ViperWriter<'a>) {
        debug!("emitting!");

        macro_rules! w {
            () => {};
            ($str:literal) => {{
                write!(writer.output.buf, $str).unwrap();
            }};
            ($e:expr) => {
                writer.emit($e);
            };
            ($str:literal, $($t:tt)*) => {{
                write!(writer.output.buf, $str).unwrap();
                w!($($t)*);
            }};
            ($e:expr, $($t:tt)*) => {{
                writer.emit($e);
                w!($($t)*);
            }};
        }

        match &writer.arena[vexpr].data {
            Exp::Bin { op, left, right } => w!("(", left, " {op} ", right, ")"),
            Exp::Un { op, exp } => w!("{op}", exp),
            Exp::MagicWand(w) => w!("(", &w.left, " --* ", &w.right, ")"),
            Exp::Literal(l) => w!("{l}"),
            Exp::AccessPredicate(_) => todo!(),
            Exp::Perm(_) => todo!(),
            Exp::FuncApp { funcname, args } => {
                w!("{funcname}(");
                let mut first = true;
                for arg in args {
                    if !first {
                        w!(", ");
                    }
                    first = false;
                    w!(arg);
                }
                w!(")");
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
                        w!(&f.rcr, ".{name}")
                    }
                    LocationAccess::Predicate(_) => todo!(),
                },
            },
            Exp::Cond { cond, thn, els } => {
                // w!("(", cond, " ? ", thn, " : ", els, ")");
                let indent = " ".repeat(writer.indentation + 2);
                writer.indentation += 4;
                w!("(", cond, "\n{indent}? ", thn, "\n{indent}: ", els, ")");
                writer.indentation -= 4;
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
                let indent = " ".repeat(writer.indentation);
                w!("(let {name} == (", exp, ") in \n{indent}", body, ")")
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
                w!("({q} ");
                let mut first = true;
                for var in variables {
                    if !first {
                        w!(", ");
                    }
                    first = false;
                    let name = &var.name;
                    let ty = &var.typ;
                    w!("{name}: ", ty)
                }
                w!(" :: ", exp, ")");
            }
            Exp::Quantifier(QuantifierExp::ForPerm {
                variables,
                resource,
                exp,
            }) => todo!(),
            Exp::AbstractLocalVar(v) => match v {
                AbstractLocalVar::LocalVar(l) => {
                    let name = &l.name;
                    w!("{name}")
                }
                AbstractLocalVar::Result { typ } => w!("result"),
            },
            Exp::Seq(s) => match s {
                SeqExp::Empty { elem_typ } => w!("Seq[", elem_typ, "]()"),
                SeqExp::Explicit { elems } => {
                    w!("Seq(");
                    let mut first = true;
                    for e in elems {
                        if !first {
                            w!(", ");
                        }
                        first = false;
                        w!(e);
                    }
                    w!(")");
                }
                SeqExp::Range { low, high } => todo!(),
                SeqExp::Append { left, right } => todo!(),
                SeqExp::Index { s, idx } => w!(s, "[", idx, "]"),
                SeqExp::Take { s, n } => w!(s, "[", "..", n, "]"),
                SeqExp::Drop { s, n } => w!(s, "[", n, "..", "]"),
                SeqExp::Contains { elem, s } => todo!(),
                SeqExp::Update { s, idx, elem } => todo!(),
                SeqExp::Length { s } => w!("|", s, "|"),
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
    fn emit<'a>(elem: &Self, writer: &mut ViperWriter<'a>) {
        write!(writer.output.buf, "{elem}").unwrap();
    }
}
