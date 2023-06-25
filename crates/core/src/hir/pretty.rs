use itertools::Itertools;

use crate::{
    def::Name,
    hir::QuantifierOver,
    types::{TypeData, TypeId, TDK},
};

use super::{pretty, BuiltinExpr, Expr, ExprData, ExprIdx, Literal, Param, TypeSrc, VariableIdx};

pub trait PrettyPrint {
    fn resolve_var(&self, idx: VariableIdx) -> Name;
    fn resolve_var_ty(&self, db: &dyn crate::Db, idx: VariableIdx) -> TypeId;
    fn resolve_ty(&self, ty: TypeId) -> TypeData;
    fn resolve_src_ty(&self, db: &dyn crate::Db, ts: TypeSrc) -> TypeId;
    fn resolve_expr(&self, idx: ExprIdx) -> &Expr;
}

use expr as pp_expr;
use params as pp_params;
use ty as pp_ty;

pub fn params(
    pp: &impl PrettyPrint,
    db: &dyn crate::Db,
    strip_ghost: bool,
    params: impl IntoIterator<Item = Param<Name, TypeId>>,
) -> String {
    let params = params
        .into_iter()
        .map(|param| format!("{}: {}", param.name, pp_ty(pp, db, strip_ghost, param.ty)))
        .format(", ");
    format!("({params})")
}
pub fn ty(pp: &impl PrettyPrint, db: &dyn crate::Db, strip_ghost: bool, ty: TypeId) -> String {
    let rty = pp.resolve_ty(ty);

    let s = match rty.kind {
        TDK::Error => "Error".to_string(),
        TDK::Void => "void".to_string(),
        TDK::Free => "free".to_string(),
        TDK::Generic(g) => {
            if let Some(g) = g.name(db) {
                g.to_string()
            } else {
                "<generic>".to_string()
            }
        }
        TDK::Ref { is_mut, inner } => {
            format!("&{}{}", if is_mut { "mut " } else { "" }, pp_ty(pp, db, false, inner))
        }
        TDK::Optional(inner) => format!("?{}", pp_ty(pp, db, false, inner)),
        TDK::Primitive(t) => format!("{t:?}").to_lowercase(),
        TDK::Adt(s) => {
            let name = s.name(db);
            let gargs = s.generic_args(db).map(|ty| pp_ty(pp, db, false, ty)).join(", ");
            let gargs = if gargs.is_empty() { gargs } else { format!("[{gargs}]") };
            format!("{name}{gargs}")
        }
        TDK::Builtin(b, args) => {
            format!(
                "{}[{}]",
                b.name(),
                args.args(db).iter().map(|arg| pp_ty(pp, db, false, *arg)).format(", ")
            )
        }
        TDK::Null => "null".to_string(),
        TDK::Function { attrs, name, params, return_ty } => {
            let is_ghost = attrs.is_ghost();

            let mut attrs = attrs.to_string();
            if !attrs.is_empty() {
                attrs.push(' ');
            }
            let name = name.as_ref().map(|name| format!(" {name}")).unwrap_or_default();
            let params = pp_params(
                pp,
                db,
                is_ghost,
                params.iter().map(|p| p.map_ty(|ty| pp.resolve_src_ty(db, *ty))),
            );
            let ret = if let TDK::Void = pp.resolve_ty(return_ty).kind {
                String::new()
            } else {
                let ty = pretty::ty(pp, db, is_ghost, return_ty);
                format!(" -> {ty}")
            };

            format!("{attrs}fn{name}{params}{ret}")
        }
    };
    if rty.is_ghost && !strip_ghost {
        format!("ghost {s}")
    } else {
        s
    }
}
pub fn expr(pp: &impl PrettyPrint, db: &dyn crate::Db, expr: ExprIdx) -> String {
    match &pp.resolve_expr(expr).data {
        ExprData::Literal(l) => match l {
            Literal::Null => "null".to_string(),
            Literal::Int(i) => i.to_string(),
            Literal::Bool(b) => b.to_string(),
        },
        ExprData::Self_ => "self".to_string(),
        ExprData::Ident(i) => pp.resolve_var(*i).to_string(),
        ExprData::Field { expr, field, .. } => {
            let field_name = field.name(db);
            format!("{}.{field_name}", pp_expr(pp, db, *expr))
        }
        ExprData::Adt { adt: struct_declaration, fields, .. } => format!(
            "{} {{ {} }}",
            struct_declaration.name(db),
            fields
                .iter()
                .map(|f| format!("{}: {}", f.decl.name(db), pp_expr(pp, db, f.value)))
                .format(", ")
        ),
        ExprData::NotNull(it) => format!("{}!", pp_expr(pp, db, *it)),
        ExprData::Missing => "<missing>".to_string(),
        ExprData::If(it) => format!("if {}", pp_expr(pp, db, it.condition)),
        ExprData::While(it) => {
            format!("while {}", pp_expr(pp, db, it.expr))
        }
        ExprData::For(it) => {
            format!("for {} in {}", pp.resolve_var(it.variable), pp_expr(pp, db, it.in_expr))
        }
        ExprData::Block(_block) => "<block>".to_string(),
        ExprData::Return(Some(e)) => format!("return {}", pp_expr(pp, db, *e)),
        ExprData::Return(None) => "return".to_string(),
        ExprData::Call { expr, args } => format!(
            "{}({})",
            pp_expr(pp, db, *expr),
            args.iter().map(|arg| pp_expr(pp, db, *arg)).format(", ")
        ),
        ExprData::Unary { op, inner } => {
            format!("({op} {})", pp_expr(pp, db, *inner))
        }
        ExprData::Bin { lhs, op, rhs } => {
            format!("({} {op} {})", pp_expr(pp, db, *lhs), pp_expr(pp, db, *rhs))
        }
        &ExprData::Range { lhs, rhs } => {
            format!(
                "{}..{}",
                lhs.map(|e| pp_expr(pp, db, e)).unwrap_or_default(),
                rhs.map(|e| pp_expr(pp, db, e)).unwrap_or_default()
            )
        }
        &ExprData::Index { base, index } => {
            format!("{}[{}]", pp_expr(pp, db, base), pp_expr(pp, db, index))
        }
        ExprData::List { elems } => {
            format!("[{}]", elems.iter().map(|e| pp_expr(pp, db, *e)).format(", "))
        }
        ExprData::Ref { is_mut, expr } => {
            format!("&{}{}", if *is_mut { "mut" } else { "" }, pp_expr(pp, db, *expr))
        }
        ExprData::Quantifier { quantifier, over, expr } => {
            let over = match over {
                QuantifierOver::Vars(vars) => pp_params(
                    pp,
                    db,
                    true,
                    vars.iter().map(|&var| Param {
                        is_ghost: false,
                        name: pp.resolve_var(var),
                        ty: pp.resolve_var_ty(db, var),
                    }),
                ),
                QuantifierOver::In(var, over) => {
                    format!(" {} in {}", pp.resolve_var(*var), pp_expr(pp, db, *over))
                }
            };
            format!("{quantifier}{over} {{ {} }}", pp_expr(pp, db, *expr))
        }
        ExprData::Result => "result".to_string(),
        ExprData::Builtin(b) => match b {
            BuiltinExpr::RangeMin(r) => format!("#range-min({})", pp_expr(pp, db, *r)),
            BuiltinExpr::RangeMax(r) => format!("#range-max({})", pp_expr(pp, db, *r)),
            BuiltinExpr::InRange(idx, r) => {
                format!("#in-range({}, {})", pp_expr(pp, db, *idx), pp_expr(pp, db, *r))
            }
        },
    }
}
