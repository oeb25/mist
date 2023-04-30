use std::{collections::HashMap, fmt::Write};

use derive_more::From;
use derive_new::new;
use itertools::Itertools;
use la_arena::ArenaMap;
use mist_core::{hir, mir};
use mist_syntax::{ast::Spanned, SourceSpan};
use silvers::{
    expression::{AbstractLocalVar, Exp, LocationAccess, QuantifierExp, ResourceAccess, SeqExp},
    program::{Domain, ExtensionMember, Field, Function, Method, Predicate, Program},
    typ::Type,
};

use crate::lower::{ViperBody, ViperLowerError, ViperLowerErrors, ViperLowerer, ViperSourceMap};

#[salsa::tracked]
pub fn viper_file(
    db: &dyn crate::Db,
    program: hir::Program,
) -> Result<(Program<VExprId>, ViperBody, ViperSourceMap), ViperLowerError> {
    let mut domains = vec![];
    let mut fields = vec![];
    let mut predicates = vec![];
    let mut methods = vec![];
    let mut functions = vec![];
    let mut extensions = vec![];

    let mut lowerer = ViperLowerer::new();

    for &item_id in program.items(db) {
        let Some(item) = hir::item(db, program, item_id) else { continue };
        let Some((cx, _source_map)) = hir::item_lower(db, program, item_id, item) else { continue };
        let (mir, _mir_source_map) = mir::lower_item(db, cx.clone());
        match internal_viper_item(db, cx, &mut lowerer, item, &mir) {
            Ok(items) => {
                for item in items {
                    match item {
                        ViperItem::Domain(it) => domains.push(it),
                        ViperItem::Field(it) => fields.push(it),
                        ViperItem::Function(it) => functions.push(it),
                        ViperItem::Predicate(it) => predicates.push(it),
                        ViperItem::Method(it) => methods.push(it),
                        ViperItem::ExtensionMember(it) => extensions.push(it),
                    }
                }
            }
            Err(err) => {
                ViperLowerErrors::push(db, err.clone());
                return Err(err);
            }
        }
    }

    let program = Program {
        domains,
        fields,
        functions,
        predicates,
        methods,
        extensions,
    };
    let (viper_body, viper_source_map) = lowerer.finish();

    Ok((program, viper_body, viper_source_map))
}

pub fn viper_item(
    db: &dyn crate::Db,
    cx: hir::ItemContext,
    item: hir::Item,
    mir: &mir::Body,
) -> Result<(Vec<ViperItem<VExprId>>, ViperBody, ViperSourceMap), ViperLowerError> {
    let mut lowerer = ViperLowerer::new();
    let items = internal_viper_item(db, cx, &mut lowerer, item, mir)?;
    let (viper_body, viper_source_map) = lowerer.finish();
    Ok((items, viper_body, viper_source_map))
}
fn internal_viper_item(
    db: &dyn crate::Db,
    cx: hir::ItemContext,
    lowerer: &mut ViperLowerer,
    item: hir::Item,
    mir: &mir::Body,
) -> Result<Vec<ViperItem<VExprId>>, ViperLowerError> {
    match item {
        hir::Item::Type(ty_decl) => match ty_decl.data(db) {
            hir::TypeDeclData::Struct(s) => {
                let mut lower = lowerer.body_lower(db, &cx, mir, false);
                lower.struct_lower(s, [])
            }
        },
        hir::Item::TypeInvariant(_) => Ok(vec![]),
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
                let body = mir
                    .body_block()
                    .map(|body| lower.pure_lower(body))
                    .transpose()?;

                let func = Function {
                    name: function.name(db).to_string(),
                    formal_args,
                    typ: ret_ty
                        .ok_or_else(|| ViperLowerError::NotYetImplemented {
                            msg: "function had no return type".to_owned(),
                            item_id: cx.item_id(),
                            block_or_inst: None,
                            span: Some(function.name(db).span()),
                        })?
                        .1
                        .vty,
                    pres,
                    posts,
                    body,
                };

                Ok(vec![func.into()])
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

                Ok(vec![method.into()])
            }
        }
    }
}

#[derive(new, Debug, Clone, From)]
pub enum ViperItem<E> {
    Domain(Domain<E>),
    Field(Field),
    Function(Function<E>),
    Predicate(Predicate<E>),
    Method(Method<E>),
    ExtensionMember(ExtensionMember),
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
pub struct ViperWriter<Cx> {
    cx: Cx,
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
    pub fn trace_expr(&self, span: SourceSpan) -> Option<VExprId> {
        self.expr_map_back
            .iter()
            .sorted_by_key(|(s, _)| *s)
            .find(|(s, _)| s.overlaps(span))
            .map(|(_, exp)| *exp)
    }
}

impl ViperOutput {
    pub fn generate<Cx, E: ViperWrite<Cx>>(cx: Cx, x: &E) -> ViperOutput {
        let mut writer = ViperWriter::new(cx);
        writer.emit(x);
        writer.finish()
    }
}

impl<Cx> ViperWriter<Cx> {
    pub(crate) fn finish(self) -> ViperOutput {
        self.output
    }
    pub(crate) fn emit<E: ViperWrite<Cx>>(&mut self, elem: &E) {
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
pub trait ViperWrite<Cx> {
    fn emit(elem: &Self, w: &mut ViperWriter<Cx>);
    fn register(elem: &Self, w: &mut ViperWriter<Cx>, span: SourceSpan) {
        let _ = (elem, w, span);
    }
}

mod write_impl {
    use silvers::{
        ast::Declaration,
        expression::{
            FieldAccess, FieldAccessPredicate, LocalVar, PermExp, PredicateAccess,
            PredicateAccessPredicate,
        },
        program::{AnyLocalVarDecl, LocalVarDecl, Method, Program},
        statement::{Seqn, Stmt},
    };

    use super::*;

    impl ViperWrite<&'_ ViperBody> for VExprId {
        fn emit(&vexpr: &Self, w: &mut ViperWriter<&'_ ViperBody>) {
            Exp::emit(&w.cx[vexpr].data, w)
        }

        fn register(&vexpr: &Self, writer: &mut ViperWriter<&'_ ViperBody>, span: SourceSpan) {
            writer.output.expr_map.insert(vexpr, span);
            writer.output.expr_map_back.insert(span, vexpr);
        }
    }

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

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for Exp<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            match elem {
                Exp::Bin { op, left, right } => w!(w, "(", left, " {op} ", right, ")"),
                Exp::Un { op, exp } => w!(w, "{op}", exp),
                Exp::MagicWand(m) => w!(w, "(", &m.left, " --* ", &m.right, ")"),
                Exp::Literal(l) => w!(w, "{l}"),
                Exp::AccessPredicate(acc) => match acc {
                    silvers::expression::AccessPredicate::Field(f) => w!(w, "acc(", f, ")"),
                    silvers::expression::AccessPredicate::Predicate(_) => {
                        w!(w, " // TODO: AccessPredicate::Predicate")
                    }
                },
                Exp::Perm(perm) => w!(w, perm),
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
                        LocationAccess::Field(f) => w!(w, f),
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
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for PermExp<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            match elem {
                PermExp::Wildcard => w!(w, "*"),
                PermExp::Full => w!(w, "write"),
                PermExp::No => w!(w, " // TODO: PermExp::No"),
                PermExp::Epsilon => w!(w, " // TODO: PermExp::Epsilon"),
                PermExp::Bin { op, left, right } => w!(w, " // TODO: PermExp::Bin"),
                PermExp::Current { res } => w!(w, " // TODO: PermExp::Current"),
            }
        }
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for Stmt<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
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

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for Seqn<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
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

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for Declaration<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            match elem {
                Declaration::LocalVar(v) => w!(w, "var ", v),
                Declaration::DomainAxiom(_) => w!(w, "// TODO: DomainAxiom"),
                Declaration::DomainFunc(_) => w!(w, "// TODO: DomainFunc"),
                Declaration::Label(_) => w!(w, "// TODO: Label"),
            }
        }
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for PredicateAccessPredicate<E> {
        fn emit(_elem: &Self, w: &mut ViperWriter<Cx>) {
            w!(w, "// TODO: PredicateAccessPredicate");
        }
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for PredicateAccess<E> {
        fn emit(_elem: &Self, w: &mut ViperWriter<Cx>) {
            w!(w, "// TODO: PredicateAccess");
        }
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for FieldAccessPredicate<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            w!(w, &elem.loc, ", ", &elem.perm)
        }
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for FieldAccess<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            let name = &elem.field;
            w!(w, &elem.rcr, ".{name}")
        }
    }

    impl<Cx> ViperWrite<Cx> for AnyLocalVarDecl {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            match elem {
                AnyLocalVarDecl::UnnamedLocalVarDecl { .. } => todo!(),
                AnyLocalVarDecl::LocalVarDecl(v) => w!(w, v),
            }
        }
    }

    impl<Cx> ViperWrite<Cx> for LocalVar {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            let name = &elem.name;
            w!(w, "{name}");
        }
    }

    impl<Cx> ViperWrite<Cx> for LocalVarDecl {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            let name = &elem.name;
            let typ = &elem.typ;
            w!(w, "{name}: {typ}");
        }
    }

    impl<Cx> ViperWrite<Cx> for Type {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            w!(w, "{elem}");
        }
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for Domain<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {}
    }

    impl<Cx> ViperWrite<Cx> for Field {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            let name = &elem.name;
            wln!(w, "field {name}: ", &elem.typ);
        }
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for Function<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
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

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for Predicate<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            let name = &elem.name;
            w!(w, "predicate {name}(");
            let mut first = true;
            for arg in &elem.formal_args {
                if !first {
                    w!(w, ", ");
                }
                first = false;
                w!(w, arg);
            }
            w!(w, ")");
            if let Some(b) = &elem.body {
                wln!(w, " {{");
                w.indent(|w| {
                    wln!(w, b);
                });
                wln!(w, "}}");
            }
        }
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for Method<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
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

    impl<Cx> ViperWrite<Cx> for ExtensionMember {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {}
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for ViperItem<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            match elem {
                ViperItem::Domain(it) => Domain::emit(it, w),
                ViperItem::Field(it) => Field::emit(it, w),
                ViperItem::Function(it) => Function::emit(it, w),
                ViperItem::Predicate(it) => Predicate::emit(it, w),
                ViperItem::Method(it) => Method::emit(it, w),
                ViperItem::ExtensionMember(it) => ExtensionMember::emit(it, w),
            }
        }
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for Program<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            for it in &elem.domains {
                wln!(w, it);
            }
            for it in &elem.fields {
                wln!(w, it);
            }
            for it in &elem.functions {
                wln!(w, it);
            }
            for it in &elem.predicates {
                wln!(w, it);
            }
            for it in &elem.methods {
                wln!(w, it);
            }
            for it in &elem.extensions {
                wln!(w, it);
            }
        }
    }
}
