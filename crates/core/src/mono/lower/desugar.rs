#[cfg(test)]
mod tests;

use crate::{
    mono::{
        exprs::{BuiltinExpr, ExprData, ExprFunction, ExprPtr, Field, QuantifierOver},
        types::{Type, TypeData},
    },
    types::{BuiltinField, BuiltinKind, RangeField, SetField::Contains},
};

use super::builder::{build, Builder};

pub fn desugar_expr(db: &dyn crate::Db, expr: ExprPtr) -> ExprPtr {
    let builder = Builder { db };

    macro_rules! desugar {
        ($($f:expr),+) => {{
            $(let expr = $f(db, &builder, expr);)+
            expr
        }};
    }

    desugar!(desugar_quantifier_in, desugar_for)
}

fn desugar_quantifier_in(db: &dyn crate::Db, b: &Builder, src: ExprPtr) -> ExprPtr {
    let ExprData::Quantifier { quantifier, over: QuantifierOver::In(var, in_expr), expr: body }
        = src.data(db) else { return src };

    let over = QuantifierOver::Vars(vec![var]);

    let var_expr = b.var_expr(src, var);
    let condition = match in_expr.ty().kind(db) {
        TypeData::Builtin(bit) => match bit.kind(db) {
            BuiltinKind::Set => ExprData::Call {
                fun: ExprFunction::Builtin(BuiltinField::Set(in_expr.ty(), Contains)),
                args: [in_expr, var_expr].to_vec(),
            },
            BuiltinKind::Range => ExprData::Builtin(BuiltinExpr::InRange(var_expr, in_expr)),
            // TODO
            _ => b.lit(src, false).data(db),
        },
        _ => b.lit(src, false).data(db),
    };
    let condition = b.alloc(in_expr, Type::bool(db), condition);
    let else_branch = b.lit(src, true);

    let new_body = build!(b, src, if condition { body } else { else_branch });
    b.quantifier(src, quantifier, over, new_body)
}

/// Desugar `for i in iter { ...body... }` into:
/// - `let i = iter.min`
/// - `while i < iter.max`
///     - `inv iter.min <= i`
///     - `inv iter.max <= max ==> i <= iter.max`
///         - Since we don't have `==>` rewrite to:
///         - `!(min <= max) || idx <= max`, and then,
///         - `min > max || idx <= max`
///     - `{`
///         - `...body...`
///         - `i = i + 1`
///     - `}`
fn desugar_for(db: &dyn crate::Db, b: &Builder, src: ExprPtr) -> ExprPtr {
    let ExprData::For(it) = src.data(db) else {
        return src
    };

    let var = b.var_expr(src, it.variable);
    let iter = it.in_expr;

    let min_field = Field::Builtin(BuiltinField::Range(iter.ty(), RangeField::Min), Type::int(db));
    let iter_min = b.field(src, iter, min_field);
    let max_field = Field::Builtin(BuiltinField::Range(iter.ty(), RangeField::Max), Type::int(db));
    let iter_max = b.field(src, iter, max_field);

    let let_stmt = {
        let var_var = it.variable;
        build!(b, src, let var_var = iter_min)
    };

    let update_expr = build!(b, src, var = { var + 1 });

    let condition = build!(b, src, var < iter_max);
    let bound_invs = [
        build!(b, src, iter_min <= var),
        build!(b, src, { iter_min > iter_max } || { var <= iter_max }),
    ]
    .to_vec();
    let mut invariants = it.invariants.clone();
    invariants.insert(0, bound_invs);
    let decreases = Default::default();
    let body = b.block(src, [it.body, update_expr].map(|e| b.expr_stmt(e)).to_vec(), None);
    let while_loop = b.while_expr(src, condition, invariants, decreases, body);

    b.block(src, [let_stmt, b.expr_stmt(while_loop)].to_vec(), None)
}
