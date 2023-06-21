use mist_syntax::ast::operators::{ArithOp, BinaryOp, LogicOp};

use crate::{
    hir::{IfExpr, Let},
    types::builtin::{bool, int, void},
};

use super::{
    Block, BuiltinExpr, Decreases, ExprData, ItemContext, Literal, QuantifierOver, Statement,
    StatementData, WhileExpr,
};

pub fn desugar(db: &dyn crate::Db, cx: &mut ItemContext) {
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
                let vars = vec![var];

                let var_expr = alloc_expr!(ExprData::Ident(var), cx.var_ty(db, var).id());
                let condition =
                    alloc_expr!(ExprData::Builtin(BuiltinExpr::InRange(var_expr, in_expr)), bool());
                let true_expr = alloc_expr!(ExprData::Literal(Literal::Bool(true)), bool());
                let body_expr = alloc_expr!(
                    ExprData::If(IfExpr {
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
                        over: QuantifierOver::Vars(vars),
                        expr: body_expr
                    },
                    bool()
                )
            }
            ExprData::For(it) => {
                // TODO: Alloc it.in_expr to a fresh local, in case it might not be pure
                let var_min_expr =
                    alloc_expr!(ExprData::Builtin(BuiltinExpr::RangeMin(it.in_expr)), int());
                let var_max_expr =
                    alloc_expr!(ExprData::Builtin(BuiltinExpr::RangeMax(it.in_expr)), int());
                let let_var_stmt = cx.stmt_arena.alloc(Statement::new(StatementData::Let(Let {
                    variable: Some(it.variable),
                    initializer: var_min_expr,
                })));
                let var_expr =
                    alloc_expr!(ExprData::Ident(it.variable), cx.var_ty(db, it.variable).id());
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
                let update_stmt =
                    cx.stmt_arena.alloc(Statement::new(StatementData::Expr(update_expr)));
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
                let while_body = alloc_expr!(
                    ExprData::Block(Block {
                        stmts: vec![
                            cx.stmt_arena.alloc(Statement::new(StatementData::Expr(it.body))),
                            update_stmt,
                        ],
                        tail_expr: None,
                        return_ty: void(),
                    }),
                    void()
                );
                let while_expr = alloc_expr!(
                    ExprData::While(WhileExpr {
                        expr: cond_expr,
                        invariants,
                        decreases: Decreases::Unspecified,
                        body: while_body,
                    }),
                    void()
                );
                let while_stmt =
                    cx.stmt_arena.alloc(Statement::new(StatementData::Expr(while_expr)));

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
