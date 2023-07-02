#[cfg(test)]
mod tests;

use mist_syntax::ast::operators::{ArithOp, BinaryOp, LogicOp};

use crate::{
    mono::{
        exprs::{
            BuiltinExpr, ExprData, ExprFunction, ExprPtr, Field, IfExpr, Let, QuantifierOver,
            StatementData,
        },
        types::{Type, TypeData},
    },
    types::{BuiltinField, BuiltinKind, RangeField, SetField::Contains},
};

use super::builder::Builder;

macro_rules! build {
    ($b:expr, $src:expr, $e:literal) => {
        $b.lit($src, $e)
    };
    ($b:expr, $src:expr, $e:ident) => {
        $e
    };
    ($b:expr, $src:expr, $l:tt + $r:tt) => {{
        let lhs = build!($b, $src, $l);
        let rhs = build!($b, $src, $r);
        $b.alloc(
            $src,
            Type::int($b.db),
            ExprData::Bin { lhs, op: BinaryOp::ArithOp(ArithOp::Add), rhs },
        )
    }};
    ($b:expr, $src:expr, $l:tt = $r:tt) => {{
        let lhs = build!($b, $src, $l);
        let rhs = build!($b, $src, $r);
        $b.alloc($src, Type::void($b.db), ExprData::Bin { lhs, op: BinaryOp::Assignment, rhs })
    }};
    ($b:expr, $src:expr, $l:tt || $r:tt) => {{
        let lhs = build!($b, $src, $l);
        let rhs = build!($b, $src, $r);
        $b.alloc($src, Type::bool($b.db), ExprData::Bin { lhs, op: BinaryOp::LogicOp(LogicOp::Or), rhs })
    }};
    ($b:expr, $src:expr, $l:tt < $r:tt) => {{
        let lhs = build!($b, $src, $l);
        let rhs = build!($b, $src, $r);
        $b.alloc($src, Type::bool($b.db), ExprData::Bin { lhs, op: BinaryOp::lt(), rhs })
    }};
    ($b:expr, $src:expr, $l:tt <= $r:tt) => {{
        let lhs = build!($b, $src, $l);
        let rhs = build!($b, $src, $r);
        $b.alloc($src, Type::bool($b.db), ExprData::Bin { lhs, op: BinaryOp::le(), rhs })
    }};
    ($b:expr, $src:expr, $l:tt >= $r:tt) => {{
        let lhs = build!($b, $src, $l);
        let rhs = build!($b, $src, $r);
        $b.alloc($src, Type::bool($b.db), ExprData::Bin { lhs, op: BinaryOp::ge(), rhs })
    }};
    ($b:expr, $src:expr, if $cond:tt { $then:tt } else { $else:tt }) => {{
        let if_expr = ExprData::If(IfExpr { condition: $cond, then_branch: $then, else_branch: $else });
        $b.alloc($src, Type::bool($b.db), if_expr)
    }};
    ($b:expr, $src:expr, let $var:tt = $val:tt) => {{
        $b.stmt($src.def, StatementData::Let(Let { variable: Some($var), initializer: $val }))
    }};
    ($b:expr, $src:expr, { $($tt:tt)* }) => {
        build!($b, $src, $($tt)*)
    };
}

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
                args: vec![in_expr, var_expr],
            },
            BuiltinKind::Range => ExprData::Builtin(BuiltinExpr::InRange(var_expr, in_expr)),
            // TODO
            _ => b.lit(src, false).data(db),
        },
        _ => b.lit(src, false).data(db),
    };
    let condition = b.alloc(in_expr, Type::bool(db), condition);
    let then_branch = body;
    let else_branch = Some(b.lit(src, true));

    let new_body = build!(b, src, if condition { then_branch } else { else_branch });

    b.alloc(src, Type::bool(db), ExprData::Quantifier { quantifier, over, expr: new_body })
}

/// Desugar `for i in iter { ...body... }` into:
/// - `let i = iter.min`
/// - `while i < iter.max`
///     - `inv iter.min <= i`
///     - `inv iter.max < max ==> i <= iter.max`
///         - Since we don't have `==>` rewrite to:
///         - `!(min < max) || idx <= max`, and then,
///         - `min >= max || idx <= max`
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

    let var_var = it.variable;
    let let_stmt = build!(b, src, let var_var = iter_min);

    let update_expr = build!(b, src, var = { var + 1 });

    let while_expr = build!(b, src, var < iter_max);
    let invariants = [[
        build!(b, src, iter_min <= var),
        build!(b, src, { iter_min >= iter_max } || { var <= iter_max }),
    ]
    .to_vec()]
    .to_vec();
    let decreases = Default::default();
    let body = b.block(src, [it.body, update_expr].map(|e| b.expr_stmt(e)).to_vec(), None);
    let while_loop = b.while_expr(src, while_expr, invariants, decreases, body);

    b.block(src, [let_stmt, b.expr_stmt(while_loop)].to_vec(), None)
}
