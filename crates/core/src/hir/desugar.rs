use mist_syntax::{
    ast::operators::{ArithOp, BinaryOp, LogicOp},
    SourceSpan,
};

use crate::{
    hir::{IfExpr, Param},
    types::builtin::{bool, int, void},
};

use super::{
    Block, BuiltinExpr, Decreases, ExprData, ItemContext, Literal, QuantifierOver, Statement,
    StatementData, WhileStmt,
};

pub fn desugar(cx: &mut ItemContext) {
    let mut desugar_queue = Vec::new();

    for (eid, expr) in cx.expr_arena.iter() {
        if cx.desugared.contains_idx(eid) {
            continue;
        }

        match &expr.data {
            ExprData::Quantifier { over: QuantifierOver::In(_, _), .. } | ExprData::For(_) => {
                desugar_queue.push(eid)
            }
            _ => continue,
        }
    }

    for eid in desugar_queue {
        macro_rules! alloc_expr {
            ($e:expr, $t:expr) => {{
                let new_idx = cx.expr_arena.alloc($e.typed($t));
                cx.desugared_back.insert(new_idx, eid);
                new_idx
            }};
        }

        let new_eid = match cx.expr_arena[eid].data.clone() {
            ExprData::Quantifier { quantifier, over: QuantifierOver::In(var, in_expr), expr } => {
                // TODO: this is a bad span
                let span = SourceSpan::new_start_end(0, 0);

                let params =
                    vec![Param { is_ghost: false, name: var.idx(), ty: cx.var_ty_src(var) }];

                let var_expr = alloc_expr!(ExprData::Ident(var), cx.var_ty(var.idx()).id());
                let condition =
                    alloc_expr!(ExprData::Builtin(BuiltinExpr::InRange(var_expr, in_expr)), bool());
                let true_expr = alloc_expr!(ExprData::Literal(Literal::Bool(true)), bool());
                let body_expr = alloc_expr!(
                    ExprData::If(IfExpr {
                        if_span: span,
                        is_ghost: true,
                        return_ty: bool(),
                        condition,
                        then_branch: expr,
                        else_branch: Some(true_expr)
                    }),
                    bool()
                );

                alloc_expr!(
                    ExprData::Quantifier {
                        quantifier,
                        over: QuantifierOver::Params(params),
                        expr: body_expr
                    },
                    bool()
                )
            }
            ExprData::For(it) => {
                // TODO: this is a bad span
                let span = SourceSpan::new_start_end(0, 0);
                // TODO: Alloc it.in_expr to a fresh local, in case it might not be pure
                let var_min_expr =
                    alloc_expr!(ExprData::Builtin(BuiltinExpr::RangeMin(it.in_expr)), int());
                let var_max_expr =
                    alloc_expr!(ExprData::Builtin(BuiltinExpr::RangeMax(it.in_expr)), int());
                let let_var_stmt = Statement::new(
                    span,
                    StatementData::Let {
                        variable: it.variable,
                        explicit_ty: None,
                        initializer: var_min_expr,
                    },
                );
                let var_expr =
                    alloc_expr!(ExprData::Ident(it.variable), cx.var_ty(it.variable.idx()).id());
                let cond_expr = alloc_expr!(
                    ExprData::Builtin(BuiltinExpr::InRange(var_expr, it.in_expr)),
                    bool()
                );
                let update_expr = {
                    let one = alloc_expr!(ExprData::Literal(Literal::Int(1)), int());
                    let var_plus_one = alloc_expr!(
                        ExprData::Bin {
                            lhs: var_expr,
                            op: BinaryOp::ArithOp(ArithOp::Add),
                            rhs: one,
                        },
                        int()
                    );
                    alloc_expr!(
                        ExprData::Bin {
                            lhs: var_expr,
                            op: BinaryOp::Assignment,
                            rhs: var_plus_one,
                        },
                        void()
                    )
                };
                let update_stmt = Statement::new(span, StatementData::Expr(update_expr));
                let mut invariants = it.invariants.clone();
                let increasing_inv_expr = alloc_expr!(
                    ExprData::Bin { lhs: var_expr, op: BinaryOp::ge(), rhs: var_min_expr },
                    bool()
                );
                let limited_inv_expr = {
                    // NOTE: We don't have ==>, so we construct:
                    //  - min < max ==> idx <= max
                    //  - !(min < max) || idx <= max
                    //  - min >= max || idx <= max
                    let min_ge_max = alloc_expr!(
                        ExprData::Bin { lhs: var_min_expr, op: BinaryOp::ge(), rhs: var_max_expr },
                        bool()
                    );
                    let var_bounded = alloc_expr!(
                        ExprData::Bin { lhs: var_max_expr, op: BinaryOp::ge(), rhs: var_expr },
                        bool()
                    );
                    alloc_expr!(
                        ExprData::Bin {
                            lhs: min_ge_max,
                            op: BinaryOp::LogicOp(LogicOp::Or),
                            rhs: var_bounded
                        },
                        bool()
                    )
                };
                invariants.insert(0, vec![increasing_inv_expr, limited_inv_expr]);
                let while_stmt = Statement::new(
                    span,
                    StatementData::While(WhileStmt {
                        expr: cond_expr,
                        invariants,
                        decreases: Decreases::Unspecified,
                        body: Block {
                            stmts: vec![
                                Statement::new(span, StatementData::Expr(it.body)),
                                update_stmt,
                            ],
                            tail_expr: None,
                            return_ty: void(),
                        },
                    }),
                );

                alloc_expr!(
                    ExprData::Block(Block {
                        stmts: vec![let_var_stmt, while_stmt],
                        tail_expr: None,
                        return_ty: void(),
                    }),
                    void()
                )
            }
            _ => unreachable!(),
        };
        cx.desugared.insert(eid, new_eid);
        cx.desugared_back.insert(new_eid, eid);
    }
}
