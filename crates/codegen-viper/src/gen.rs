use std::{collections::HashMap, fmt::Write};

use derive_more::From;
use derive_new::new;
use itertools::Itertools;
use mist_core::{
    def, hir,
    mir::{self, pass::Pass},
    util::{impl_idx, IdxMap, IdxWrap},
};
use mist_syntax::SourceSpan;
use silvers::{
    expression::{AbstractLocalVar, Exp, LocationAccess, QuantifierExp, ResourceAccess, SeqExp},
    program::{Domain, ExtensionMember, Field, Function, Method, Predicate, Program},
    typ::Type,
};

use crate::lower::{ViperBody, ViperLowerError, ViperLowerErrors, ViperLowerer, ViperSourceMap};

type Result<T> = std::result::Result<T, ViperLowerError>;

#[salsa::tracked]
pub fn viper_file(
    db: &dyn crate::Db,
    file: hir::SourceFile,
) -> Result<(Program<VExprId>, ViperBody, ViperSourceMap)> {
    let mut domains = vec![];
    let mut fields = vec![];
    let mut predicates = vec![];
    let mut methods = vec![];
    let mut functions = vec![];
    let mut extensions = vec![];

    let mut lowerer = ViperLowerer::new();

    for def in hir::file_definitions(db, file) {
        let Some((cx, mir)) = def.hir_mir(db) else { return Err(ViperLowerError::EmptyBody) };
        let mut mir = mir.clone();
        mir::pass::FullDefaultPass::run(db, &mut mir);
        match internal_viper_item(db, cx, &mut lowerer, def, &mir) {
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

    let file = Program { domains, fields, functions, predicates, methods, extensions };
    let (viper_body, viper_source_map) = lowerer.finish();

    Ok((file, viper_body, viper_source_map))
}

#[salsa::tracked]
pub fn viper_item(
    db: &dyn crate::Db,
    def: def::Def,
) -> Result<(Vec<ViperItem<VExprId>>, ViperBody, ViperSourceMap)> {
    let Some((cx, body)) = def.hir_mir(db) else { return Err(ViperLowerError::EmptyBody) };
    let mut body = body.clone();
    mir::pass::FullDefaultPass::run(db, &mut body);
    let mut lowerer = ViperLowerer::new();
    let items = internal_viper_item(db, cx, &mut lowerer, def, &body)?;
    let (viper_body, viper_source_map) = lowerer.finish();
    Ok((items, viper_body, viper_source_map))
}
fn internal_viper_item(
    db: &dyn crate::Db,
    cx: &hir::ItemContext,
    lowerer: &mut ViperLowerer,
    def: def::Def,
    mir: &mir::Body,
) -> Result<Vec<ViperItem<VExprId>>> {
    match def.kind(db) {
        def::DefKind::Struct(s) => {
            let mut lower = lowerer.body_lower(db, cx, mir, false);
            lower.struct_lower(s, mir.invariants().iter().copied())
        }
        def::DefKind::StructField(_) => {
            // TODO: We should perhaps emit the field here instead of in struct?
            Ok(vec![])
        }
        def::DefKind::TypeInvariant(_) => Ok(vec![]),
        def::DefKind::Function(function) => {
            let is_method = !function.attrs(db).is_pure();

            let mut lower = lowerer.body_lower(db, cx, mir, is_method);

            let mut pres = vec![];
            let mut posts = vec![];

            let formal_args = mir
                .params()
                .iter()
                .map(|&s| {
                    // TODO: Don't lower explicitly from 0
                    let bid = mir::BlockId::from_raw(0.into());

                    let refe = lower.place_to_ref(bid, s.into())?;
                    let conds = lower.ty_to_condition(bid, refe, mir.slot_ty(s))?;
                    if let Some(cond) = conds.0 {
                        pres.push(cond);
                    }
                    if is_method {
                        if let Some(cond) = conds.1 {
                            posts.push(cond);
                        }
                    }

                    lower.slot_to_decl(s)
                })
                .collect::<Result<_>>()?;

            let return_ty = mir
                .result_slot()
                .map(|s| {
                    // TODO: Don't lower explicitly from 0
                    let bid = mir::BlockId::from_raw(0.into());

                    let refe = lower.place_to_ref(bid, s.into())?;
                    let conds = lower.ty_to_condition(bid, refe, mir.slot_ty(s))?;
                    if is_method {
                        if let Some(cond) = conds.0 {
                            posts.push(cond);
                        }
                    }

                    lower.slot_to_decl(s)
                })
                .transpose()?;

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

            if function.attrs(db).is_pure() {
                let body = mir.body_block().map(|body| lower.pure_lower(body)).transpose()?;

                let func = Function {
                    name: function.name(db).to_string(),
                    formal_args,
                    typ: return_ty
                        .ok_or_else(|| ViperLowerError::NotYetImplemented {
                            msg: "function had no return type".to_owned(),
                            def: cx.def(),
                            block_or_inst: None,
                            span: None,
                            // TODO: find a way to pass the span here
                            // span: Some(function.name(db).span()),
                        })?
                        .typ,
                    pres,
                    posts,
                    body,
                };

                Ok(vec![func.into()])
            } else {
                let formal_returns = return_ty.map(|ret| vec![ret]).unwrap_or_default();

                let method = Method {
                    name: function.name(db).to_string(),
                    formal_args,
                    formal_returns,
                    pres,
                    posts,
                    body: mir.body_block().map(|body| lower.method_lower(body)).transpose()?,
                };

                Ok(vec![method.into()])
            }
        }
    }
}

#[derive(new, Debug, Clone, PartialEq, Eq, From)]
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

impl_idx!(VExprId, VExpr, default_debug);
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
    pub expr_map: IdxMap<VExprId, SourceSpan>,
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
    pub(crate) fn finish(mut self) -> ViperOutput {
        write!(self.output.buf, "{}", include_str!("./prelude.vpr")).unwrap();
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

impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for Box<E> {
    fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
        E::emit(&**elem, w)
    }
}

mod write_impl {
    use silvers::{
        ast::Declaration,
        expression::{
            FieldAccess, FieldAccessPredicate, LocalVar, MagicWand, OldExp, PermExp,
            PredicateAccess, PredicateAccessPredicate,
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
                    silvers::expression::AccessPredicate::Predicate(p) => {
                        w!(w, p)
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
                Exp::Unfolding { acc, body } => w!(w, "(unfolding ", acc, " in ", body, ")"),
                Exp::Applying { wand, body } => w!(w, "(applying ", wand, " in ", body, ")"),
                Exp::Old(old) => match old {
                    OldExp::Old { exp } => w!(w, "old(", exp, ")"),
                    OldExp::Labelled { exp, old_label } => w!(w, "old[{old_label}](", exp, ")"),
                },
                Exp::Let { variable, exp, body } => {
                    let name = &variable.name;
                    w!(w, "(let {name} == (");
                    w.indent(|w| wln!(w, exp, ") in"));
                    w!(w, body, ")");
                }
                Exp::Quantifier(
                    q @ QuantifierExp::Exists { variables, triggers: _, exp }
                    | q @ QuantifierExp::Forall { variables, triggers: _, exp },
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
                    SeqExp::Append { left, right } => w!(w, "(", left, " ++ ", right, ")"),
                    SeqExp::Index { s, idx } => w!(w, s, "[", idx, "]"),
                    SeqExp::Take { s, n } => w!(w, s, "[", "..", n, "]"),
                    SeqExp::Drop { s, n } => w!(w, s, "[", n, "..", "]"),
                    SeqExp::Contains { .. } => w!(w, "// TODO: Contains"),
                    SeqExp::Update { s, idx, elem } => w!(w, s, "[", idx, " := ", elem, "]"),
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
                PermExp::Wildcard => w!(w, "wildcard"),
                PermExp::Full => w!(w, "write"),
                PermExp::No => w!(w, "none"),
                PermExp::Epsilon => w!(w, " // TODO: PermExp::Epsilon"),
                PermExp::Bin { op, left, right } => {
                    w!(w, "(", left, " {op} ", right, ")")
                }
                PermExp::Current { res: _ } => w!(w, " // TODO: PermExp::Current"),
            }
        }
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for Stmt<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            match elem {
                Stmt::NewStmt { lhs, fields } => {
                    w!(w, lhs, " := new(");
                    let mut first = true;
                    for f in fields {
                        if !first {
                            w!(w, ", ");
                        }
                        first = false;
                        w!(w, f);
                    }
                    w!(w, ")");
                }
                Stmt::LocalVarAssign { lhs, rhs } => {
                    w!(w, lhs, " := ", rhs);
                }
                Stmt::FieldAssign { lhs, rhs } => w!(w, lhs, " := ", rhs),
                Stmt::MethodCall { method_name, args, targets } => {
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
                Stmt::Apply { exp } => w!(w, "apply ", exp),
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
                Stmt::Label(l) => {
                    let name = &l.name;
                    wln!(w, "label {name}");
                    w.indent(|w| {
                        for e in &l.invs {
                            wln!(w, "invariant");
                            w.indent(|w| wln!(w, e));
                        }
                    });
                }
                Stmt::Goto { target } => w!(w, "goto {target}"),
                Stmt::LocalVarDeclStmt { .. } => w!(w, "// TODO: LocalVarDeclStmt"),
                Stmt::Quasihavoc { .. } => w!(w, "// TODO: Quasihavoc"),
                Stmt::Quasihavocall { .. } => w!(w, "// TODO: Quasihavocall"),
                Stmt::Expression(_) => w!(w, "// TODO: Expression"),
            }
        }
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for MagicWand<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            w!(w, &elem.left, " --* ", &elem.right)
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
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            w!(w, "acc(", &elem.loc, ", ", &elem.perm, ")");
        }
    }

    impl<Cx, E: ViperWrite<Cx>> ViperWrite<Cx> for PredicateAccess<E> {
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            let name = &elem.predicate_name;
            w!(w, "{name}(");
            let mut first = true;
            for arg in &elem.args {
                if !first {
                    w!(w, ", ");
                }
                first = false;
                w!(w, arg);
            }
            w!(w, ")");
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
        fn emit(elem: &Self, w: &mut ViperWriter<Cx>) {
            let name = &elem.name;
            wln!(w, "domain {name} {{\n  // TODO: Domains\n}}");
        }
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
        fn emit(_elem: &Self, _w: &mut ViperWriter<Cx>) {}
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
