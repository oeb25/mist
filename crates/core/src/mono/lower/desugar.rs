use crate::{
    hir::Literal,
    mono::{
        exprs::{
            BuiltinExpr, ExprData, ExprDataWrapper, ExprFunction, ExprPtr, IfExpr, QuantifierOver,
        },
        types::{Type, TypeData},
    },
    types::{BuiltinField, BuiltinKind, SetField::Contains},
};

pub fn desugar_expr(db: &dyn crate::Db, expr: ExprPtr) -> ExprPtr {
    macro_rules! desugar {
        ($($f:expr),+) => {{
            $(let expr = $f(db, expr);)+
            expr
        }};
    }

    desugar!(desugar_quantifier_in, desugar_for)
}

fn alloc(db: &dyn crate::Db, source: ExprPtr, ty: Type, data: ExprData) -> ExprPtr {
    ExprPtr { def: source.def, id: source.id, ty, inner_data: ExprDataWrapper::new(db, data) }
}

fn desugar_quantifier_in(db: &dyn crate::Db, source: ExprPtr) -> ExprPtr {
    let ExprData::Quantifier { quantifier, over: QuantifierOver::In(var, in_expr), expr: body }
        = source.data(db) else { return source };

    let over = QuantifierOver::Vars(vec![var]);

    let var_expr = alloc(db, in_expr, var.ty(), ExprData::Ident(var));
    let condition = match in_expr.ty().kind(db) {
        TypeData::Builtin(bit) => match bit.kind(db) {
            BuiltinKind::Set => ExprData::Call {
                fun: ExprFunction::Builtin(BuiltinField::Set(in_expr.ty(), Contains)),
                args: vec![in_expr, var_expr],
            },
            BuiltinKind::Range => ExprData::Builtin(BuiltinExpr::InRange(var_expr, in_expr)),
            // TODO
            _ => ExprData::Literal(Literal::Bool(false)),
        },
        _ => ExprData::Literal(Literal::Bool(false)),
    };
    let condition = alloc(db, in_expr, Type::bool(db), condition);
    let then_branch = body;
    let else_branch =
        Some(alloc(db, source, Type::bool(db), ExprData::Literal(Literal::Bool(true))));

    let if_expr = ExprData::If(IfExpr { condition, then_branch, else_branch });
    let new_body = alloc(db, source, Type::bool(db), if_expr);

    alloc(db, source, Type::bool(db), ExprData::Quantifier { quantifier, over, expr: new_body })
}

fn desugar_for(db: &dyn crate::Db, expr: ExprPtr) -> ExprPtr {
    let ExprData::For(_it) = expr.data(db) else {
        return expr
    };

    expr
}
