use std::{collections::HashMap, fmt::Write};

use derive_more::From;
use derive_new::new;
use la_arena::ArenaMap;
use mist_core::{hir, mir};
use mist_syntax::SourceSpan;
use silvers::{
    expression::{AbstractLocalVar, Exp, LocationAccess, QuantifierExp, ResourceAccess, SeqExp},
    program::{Function, Method, Program},
    typ::Type,
};

use crate::lower::{ViperBody, ViperLowerError, ViperLowerer, ViperSourceMap};

#[salsa::tracked]
pub fn viper_file(
    db: &dyn crate::Db,
    program: hir::Program,
) -> Result<(Program<VExprId>, ViperBody, ViperSourceMap), ViperLowerError> {
    #[allow(unused)]
    let mut fields = vec![];
    #[allow(unused)]
    let mut predicates = vec![];
    #[allow(unused)]
    let mut methods = vec![];
    let mut functions = vec![];

    let mut lowerer = ViperLowerer::new();

    for &item_id in program.items(db) {
        let Some(item) = hir::item(db, program, item_id) else { continue };
        let Some((cx, _source_map)) = hir::item_lower(db, program, item_id, item) else { continue };
        let (mir, _mir_source_map) = mir::lower_item(db, cx.clone());
        let Some(viper_item) = internal_viper_item(db, cx, &mut lowerer, item, &mir)? else { continue };
        match viper_item {
            ViperItem::Function(f) => functions.push(f),
            ViperItem::Method(m) => methods.push(m),
        }
    }

    let program = Program {
        domains: vec![],
        fields,
        functions,
        predicates,
        methods,
        extensions: vec![],
    };
    let (viper_body, viper_source_map) = lowerer.finish();

    Ok((program, viper_body, viper_source_map))
}

pub fn viper_item(
    db: &dyn crate::Db,
    cx: hir::ItemContext,
    item: hir::Item,
    mir: &mir::Body,
) -> Result<Option<(ViperItem<VExprId>, ViperBody, ViperSourceMap)>, ViperLowerError> {
    let mut lowerer = ViperLowerer::new();
    if let Some(viper_item) = internal_viper_item(db, cx, &mut lowerer, item, mir)? {
        let (viper_body, viper_source_map) = lowerer.finish();
        Ok(Some((viper_item, viper_body, viper_source_map)))
    } else {
        Ok(None)
    }
}
fn internal_viper_item(
    db: &dyn crate::Db,
    cx: hir::ItemContext,
    lowerer: &mut ViperLowerer,
    item: hir::Item,
    mir: &mir::Body,
) -> Result<Option<ViperItem<VExprId>>, ViperLowerError> {
    match item {
        hir::Item::Type(ty_decl) => match ty_decl.data(db) {
            hir::TypeDeclData::Struct(_) => Ok(None),
        },
        hir::Item::TypeInvariant(_) => Ok(None),
        hir::Item::Function(function) => {
            let is_method = !function.attrs(db).is_pure();

            let mut lower = lowerer.body_lower(db, &cx, mir, is_method);

            let mut pres = vec![];
            let mut posts = vec![];

            let formal_args = mir
                .params()
                .iter()
                .map(|s| lower.slot_to_decl(*s))
                .collect();

            for &pre in mir.requires() {
                pres.push(lower.pure_lower(pre)?);
            }
            for &post in mir.ensures() {
                posts.push(lower.pure_lower(post)?);
            }
            for &inv in mir.invariants() {
                let exp = lower.pure_lower(inv)?;
                pres.push(exp);
                posts.push(exp);
            }

            let ret_ty = mir.result_slot().map(|ret| {
                let ty = mir.slot_ty(ret);
                (ret, lower.lower_type(ty))
            });

            if function.attrs(db).is_pure() {
                let func = Function {
                    name: function.name(db).to_string(),
                    formal_args,
                    typ: ret_ty.unwrap().1.vty,
                    pres,
                    posts,
                    body: mir
                        .body_block()
                        .map(|body| lower.pure_lower(body))
                        .transpose()?,
                };

                Ok(Some(func.into()))
            } else {
                let formal_returns = ret_ty
                    .map(|(ret, _ty)| vec![lower.slot_to_decl(ret)])
                    .unwrap_or_default();

                let method = Method {
                    name: function.name(db).to_string(),
                    formal_args,
                    formal_returns,
                    pres,
                    posts,
                    body: mir
                        .body_block()
                        .map(|body| lower.method_lower(body))
                        .transpose()?,
                };

                Ok(Some(method.into()))
            }
        }
    }
}

#[derive(new, Debug, Clone, From)]
pub enum ViperItem<E> {
    Function(Function<E>),
    Method(Method<E>),
}

#[derive(new, Debug, Clone)]
pub struct ViperHint {
    pub span: SourceSpan,
    pub viper: String,
}

#[salsa::accumulator]
pub struct ViperHints(ViperHint);

type VExprData = Exp<VExprId>;

pub type VExprId = la_arena::Idx<VExpr>;
#[derive(new, Debug, Clone, PartialEq, Eq, Hash, derive_more::Deref)]
pub struct VExpr {
    data: VExprData,
}

#[doc(hidden)]
#[derive(new)]
pub struct ViperWriter<'a> {
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

impl ViperOutput {
    pub fn generate<E: ViperWrite>(body: &ViperBody, x: &E) -> ViperOutput {
        let mut writer = ViperWriter::new(body);
        writer.emit(x);
        writer.finish()
    }
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

#[doc(hidden)]
pub trait ViperWrite {
    fn emit(elem: &Self, w: &mut ViperWriter);
    fn register(elem: &Self, w: &mut ViperWriter, span: SourceSpan) {
        let _ = (elem, w, span);
    }
}

mod write_impl {
    use silvers::{
        ast::Declaration,
        expression::{LocalVar, PredicateAccess, PredicateAccessPredicate},
        program::{AnyLocalVarDecl, LocalVarDecl, Method, Program},
        statement::{Seqn, Stmt},
    };

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
                Exp::AccessPredicate(_) => w!(w, "// TODO: AccessPredicate"),
                Exp::Perm(_) => w!(w, "// TODO: Perm"),
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
                Exp::DomainFuncApp { .. } => w!(w, "// TODO: DomainFuncApp"),
                Exp::BackendFuncApp { .. } => w!(w, "// TODO: BackendFuncApp"),
                Exp::LocationAccess(r) => match r {
                    ResourceAccess::Location(l) => match l {
                        LocationAccess::Field(f) => {
                            let name = &f.field;
                            w!(w, &f.rcr, ".{name}")
                        }
                        LocationAccess::Predicate(_) => w!(w, "// TODO: Predicate"),
                    },
                },
                Exp::Cond { cond, thn, els } => {
                    wln!(w, "(", cond);
                    w.indent(|w| {
                        w!(w, "? ");
                        w.indent(|w| wln!(w, thn));
                        w!(w, ": ");
                        w.indent(|w| w!(w, els, ")"));
                    })
                }
                Exp::Unfolding { .. } => w!(w, "// TODO: Unfolding"),
                Exp::Applying { .. } => w!(w, "// TODO: Applying"),
                Exp::Old(_) => w!(w, "// TODO: Old"),
                Exp::Let {
                    variable,
                    exp,
                    body,
                } => {
                    let name = &variable.name;
                    w!(w, "(let {name} == (");
                    w.indent(|w| wln!(w, exp, ") in"));
                    w!(w, body, ")");
                }
                Exp::Quantifier(
                    q @ QuantifierExp::Exists {
                        variables,
                        triggers: _,
                        exp,
                    }
                    | q @ QuantifierExp::Forall {
                        variables,
                        triggers: _,
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
                Exp::Quantifier(QuantifierExp::ForPerm { .. }) => w!(w, "// TODO: Quantifier"),
                Exp::AbstractLocalVar(v) => match v {
                    AbstractLocalVar::LocalVar(l) => {
                        let name = &l.name;
                        w!(w, "{name}")
                    }
                    AbstractLocalVar::Result { .. } => w!(w, "result"),
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
                    SeqExp::Range { .. } => w!(w, "// TODO: Range"),
                    SeqExp::Append { .. } => w!(w, "// TODO: Append"),
                    SeqExp::Index { s, idx } => w!(w, s, "[", idx, "]"),
                    SeqExp::Take { s, n } => w!(w, s, "[", "..", n, "]"),
                    SeqExp::Drop { s, n } => w!(w, s, "[", n, "..", "]"),
                    SeqExp::Contains { .. } => w!(w, "// TODO: Contains"),
                    SeqExp::Update { .. } => w!(w, "// TODO: Update"),
                    SeqExp::Length { s } => w!(w, "|", s, "|"),
                },
                Exp::Set(_) => w!(w, "// TODO: Set"),
                Exp::Multiset(_) => w!(w, "// TODO: Multiset"),
                Exp::Map(_) => w!(w, "// TODO: Map"),
            }
        }

        fn register(&vexpr: &Self, writer: &mut ViperWriter, span: SourceSpan) {
            writer.output.expr_map.insert(vexpr, span);
            writer.output.expr_map_back.insert(span, vexpr);
        }
    }

    impl<E: ViperWrite> ViperWrite for Stmt<E> {
        fn emit(elem: &Self, w: &mut ViperWriter) {
            match elem {
                Stmt::NewStmt { .. } => w!(w, "// TODO: NewStmt"),
                Stmt::LocalVarAssign { lhs, rhs } => {
                    w!(w, lhs, " := ", rhs);
                }
                Stmt::FieldAssign { .. } => w!(w, "// TODO: FieldAssign"),
                Stmt::MethodCall {
                    method_name,
                    args,
                    targets,
                } => {
                    if !targets.is_empty() {
                        let mut first = true;
                        for t in targets {
                            if !first {
                                w!(w, ", ");
                            }
                            first = false;
                            w!(w, t);
                        }
                        w!(w, " := ");
                    }
                    w!(w, "{method_name}(");
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
                Stmt::Exhale { exp } => w!(w, "exhale ", exp),
                Stmt::Inhale { exp } => w!(w, "inhale ", exp),
                Stmt::Assert { exp } => w!(w, "assert ", exp),
                Stmt::Assume { exp } => w!(w, "assume ", exp),
                Stmt::Fold { acc } => w!(w, "fold ", acc),
                Stmt::Unfold { acc } => w!(w, "unfold ", acc),
                Stmt::Package { .. } => w!(w, "// TODO: Package"),
                Stmt::Apply { .. } => w!(w, "// TODO: Apply"),
                Stmt::Seqn(s) => {
                    wln!(w, "{{");
                    w.indent(|w| w!(w, s));
                    w!(w, "}}");
                }
                Stmt::If { cond, thn, els } => {
                    wln!(w, "if (", cond, ")");
                    wln!(w, "{{");
                    w.indent(|w| w!(w, thn));
                    wln!(w, "}} else {{");
                    w.indent(|w| w!(w, els));
                    w!(w, "}}");
                }
                Stmt::While { cond, invs, body } => {
                    wln!(w, "while (", cond, ")");
                    w.indent(|w| {
                        for e in invs {
                            wln!(w, "invariant");
                            w.indent(|w| wln!(w, e));
                        }
                    });
                    wln!(w, "{{");
                    w.indent(|w| w!(w, body));
                    w!(w, "}}");
                }
                Stmt::Label(_) => w!(w, "// TODO: Label"),
                Stmt::Goto { .. } => w!(w, "// TODO: Goto"),
                Stmt::LocalVarDeclStmt { .. } => w!(w, "// TODO: LocalVarDeclStmt"),
                Stmt::Quasihavoc { .. } => w!(w, "// TODO: Quasihavoc"),
                Stmt::Quasihavocall { .. } => w!(w, "// TODO: Quasihavocall"),
                Stmt::Expression(_) => w!(w, "// TODO: Expression"),
            }
        }
    }

    impl<E: ViperWrite> ViperWrite for Seqn<E> {
        fn emit(elem: &Self, w: &mut ViperWriter) {
            for decl in &elem.scoped_seqn_declarations {
                w!(w, decl, "; ");
            }
            if !elem.scoped_seqn_declarations.is_empty() {
                wln!(w, "");
            }
            for stmt in &elem.ss {
                wln!(w, stmt);
            }
        }
    }

    impl<E: ViperWrite> ViperWrite for Declaration<E> {
        fn emit(elem: &Self, w: &mut ViperWriter) {
            match elem {
                Declaration::LocalVar(v) => w!(w, "var ", v),
                Declaration::DomainAxiom(_) => w!(w, "// TODO: DomainAxiom"),
                Declaration::DomainFunc(_) => w!(w, "// TODO: DomainFunc"),
                Declaration::Label(_) => w!(w, "// TODO: Label"),
            }
        }
    }

    impl<E: ViperWrite> ViperWrite for PredicateAccessPredicate<E> {
        fn emit(_elem: &Self, w: &mut ViperWriter) {
            w!(w, "// TODO: PredicateAccessPredicate");
        }
    }

    impl<E: ViperWrite> ViperWrite for PredicateAccess<E> {
        fn emit(_elem: &Self, w: &mut ViperWriter) {
            w!(w, "// TODO: PredicateAccess");
        }
    }

    impl ViperWrite for AnyLocalVarDecl {
        fn emit(elem: &Self, w: &mut ViperWriter) {
            match elem {
                AnyLocalVarDecl::UnnamedLocalVarDecl { .. } => todo!(),
                AnyLocalVarDecl::LocalVarDecl(v) => w!(w, v),
            }
        }
    }

    impl ViperWrite for LocalVar {
        fn emit(elem: &Self, w: &mut ViperWriter) {
            let name = &elem.name;
            w!(w, "{name}");
        }
    }

    impl ViperWrite for LocalVarDecl {
        fn emit(elem: &Self, w: &mut ViperWriter) {
            let name = &elem.name;
            let typ = &elem.typ;
            w!(w, "{name}: {typ}");
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
            w!(w, "function {name}(");
            let mut first = true;
            for arg in &elem.formal_args {
                if !first {
                    w!(w, ", ");
                }
                first = false;
                w!(w, arg);
            }
            wln!(w, "): ", &elem.typ);
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

    impl<E: ViperWrite> ViperWrite for Method<E> {
        fn emit(elem: &Self, w: &mut ViperWriter) {
            let name = &elem.name;
            w!(w, "method {name}(");
            let mut first = true;
            for arg in &elem.formal_args {
                if !first {
                    w!(w, ", ");
                }
                first = false;
                w!(w, arg);
            }
            w!(w, ")");
            if !elem.formal_returns.is_empty() {
                w!(w, " returns (");
                let mut first = true;
                for arg in &elem.formal_returns {
                    if !first {
                        w!(w, ", ");
                    }
                    first = false;
                    w!(w, arg);
                }
                w!(w, ")");
            }
            wln!(w, "");
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

    impl<E: ViperWrite> ViperWrite for ViperItem<E> {
        fn emit(elem: &Self, w: &mut ViperWriter) {
            match elem {
                ViperItem::Function(f) => Function::emit(f, w),
                ViperItem::Method(m) => Method::emit(m, w),
            }
        }
    }

    impl<E: ViperWrite> ViperWrite for Program<E> {
        fn emit(elem: &Self, w: &mut ViperWriter) {
            for f in &elem.functions {
                wln!(w, f);
            }
            for m in &elem.methods {
                wln!(w, m);
            }
        }
    }
}
