use itertools::Itertools;

use super::{
    pretty, Expr, ExprData, ExprIdx, Ident, Literal, Param, TypeData, TypeId, TypeSrcId,
    VariableIdx,
};

pub trait PrettyPrint {
    fn resolve_var(&self, idx: VariableIdx) -> Ident;
    fn resolve_var_ty(&self, idx: VariableIdx) -> TypeId;
    fn resolve_ty(&self, ty: TypeId) -> TypeData;
    fn resolve_src_ty(&self, ts: TypeSrcId) -> TypeId;
    fn resolve_expr(&self, idx: ExprIdx) -> &Expr;
}

use expr as pp_expr;
use params as pp_params;
use ty as pp_ty;

fn pp_strip_ghost(pp: &impl PrettyPrint, strip: bool, ty: TypeId) -> TypeId {
    if strip {
        match pp.resolve_ty(ty) {
            TypeData::Ghost(inner) => inner,
            _ => ty,
        }
    } else {
        ty
    }
}

pub fn params(
    pp: &impl PrettyPrint,
    db: &dyn crate::Db,
    strip_ghost: bool,
    params: impl IntoIterator<Item = Param<Ident>>,
) -> String {
    format!(
        "({})",
        params
            .into_iter()
            .map(|param| {
                let ty = pp_strip_ghost(pp, strip_ghost, pp.resolve_src_ty(param.ty));
                format!("{}: {}", param.name, pp_ty(pp, db, ty))
            })
            .format(", ")
    )
}
pub fn ty(pp: &impl PrettyPrint, db: &dyn crate::Db, ty: TypeId) -> String {
    match pp.resolve_ty(ty) {
        TypeData::Error => "Error".to_string(),
        TypeData::Void => "void".to_string(),
        TypeData::Free => "free".to_string(),
        TypeData::Ref { is_mut, inner } => {
            format!(
                "&{}{}",
                if is_mut { "mut " } else { "" },
                pp_ty(pp, db, inner)
            )
        }
        TypeData::Ghost(inner) => format!("ghost {}", pp_ty(pp, db, inner)),
        TypeData::Range(inner) => format!("range {}", pp_ty(pp, db, inner)),
        TypeData::List(inner) => format!("[{}]", pp_ty(pp, db, inner)),
        TypeData::Optional(inner) => format!("?{}", pp_ty(pp, db, inner)),
        TypeData::Primitive(t) => format!("{t:?}").to_lowercase(),
        TypeData::Struct(s) => s.name(db).to_string(),
        TypeData::Null => "null".to_string(),
        TypeData::Function {
            attrs,
            name,
            params,
            return_ty,
        } => {
            let is_ghost = attrs.is_ghost();

            let mut attrs = attrs.to_string();
            if !attrs.is_empty() {
                attrs.push(' ');
            }
            let name = name
                .as_ref()
                .map(|name| format!(" {name}"))
                .unwrap_or_default();
            let params = pp_params(pp, db, is_ghost, params);
            let ret = if let TypeData::Void = pp.resolve_ty(pp_strip_ghost(pp, true, return_ty)) {
                String::new()
            } else {
                let ty = pretty::ty(pp, db, pp_strip_ghost(pp, is_ghost, return_ty));
                format!(" -> {ty}")
            };

            format!("{attrs}fn{name}{params}{ret}")
        }
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
        ExprData::Ident(i) => pp.resolve_var(i.idx).to_string(),
        ExprData::Field {
            expr, field_name, ..
        } => format!("{}.{field_name}", pp_expr(pp, db, *expr)),
        ExprData::Struct {
            struct_declaration,
            fields,
            ..
        } => format!(
            "{} {{ {} }}",
            struct_declaration.name(db),
            fields
                .iter()
                .map(|f| format!("{}: {}", f.name, pp_expr(pp, db, f.value)))
                .format(", ")
        ),
        ExprData::NotNull(it) => format!("{}!", pp_expr(pp, db, *it)),
        ExprData::Missing => "<missing>".to_string(),
        ExprData::If(it) => format!("if {}", pp_expr(pp, db, it.condition)),
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
        ExprData::List { elems } => format!(
            "[{}]",
            elems.iter().map(|e| pp_expr(pp, db, *e)).format(", ")
        ),
        ExprData::Ref { is_mut, expr } => {
            format!(
                "&{}{}",
                if *is_mut { "mut" } else { "" },
                pp_expr(pp, db, *expr)
            )
        }
        ExprData::Quantifier {
            quantifier,
            params,
            expr,
        } => format!(
            "{quantifier}{} {{ {} }}",
            pp_params(
                pp,
                db,
                true,
                params
                    .iter()
                    .map(|param| param.map_var(|var| pp.resolve_var(*var)))
            ),
            pp_expr(pp, db, *expr)
        ),
        ExprData::Result => "result".to_string(),
    }
}
