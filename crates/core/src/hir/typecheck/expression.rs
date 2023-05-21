use std::ops::Deref;

use itertools::Itertools;
use mist_syntax::ast::{
    self,
    operators::{ArithOp, BinaryOp, CmpOp},
    HasExpr, HasName, Spanned,
};

use crate::{
    hir::{
        Expr, ExprData, ExprIdx, Field, FieldParent, Ident, IfExpr, Literal, Param, Primitive,
        Quantifier, StructExprField, TypeData, TypeId, VariableRef,
    },
    VariableDeclaration,
};

use super::{typer::builtin::*, ScopeFlags, TypeCheckErrorKind, TypeChecker, Typed};

pub fn check_opt(
    tc: &mut TypeChecker,
    fallback_span: impl Spanned,
    expr: Option<ast::Expr>,
) -> ExprIdx {
    if let Some(expr) = expr {
        check(tc, expr)
    } else {
        tc.expr_error(
            fallback_span.span(),
            None,
            None,
            TypeCheckErrorKind::MissingExpression,
        )
    }
}
pub fn check_inner(tc: &mut TypeChecker, expr: &impl HasExpr) -> ExprIdx {
    if let Some(expr) = expr.expr() {
        check(tc, expr)
    } else {
        tc.expr_error(
            expr.span(),
            None,
            None,
            TypeCheckErrorKind::MissingExpression,
        )
    }
}
pub fn check(tc: &mut TypeChecker, expr: ast::Expr) -> ExprIdx {
    let new = match &expr {
        ast::Expr::Literal(it) => match it.kind() {
            ast::LiteralKind::IntNumber(s) => {
                ExprData::Literal(Literal::Int(s.to_string().parse().unwrap())).typed(int())
            }
            ast::LiteralKind::Bool(b) => ExprData::Literal(Literal::Bool(b)).typed(bool()),
        },
        ast::Expr::IfExpr(it) => return check_if_expr(tc, it.clone()),
        ast::Expr::WhileExpr(_) => todo!(),
        ast::Expr::PrefixExpr(it) => {
            let (_op_token, op) = if let Some(op) = it.op_details() {
                op
            } else {
                todo!("{it:#?}")
            };
            let inner = check_inner(tc, it);
            let inner_span = tc.expr_span(inner);
            let inner_ty = tc.expr_ty(inner);

            let is_ghost = tc.is_ghost(inner);

            let ty: TypeId = match op {
                ast::operators::UnaryOp::Not => {
                    tc.expect_ty(inner_span, bool(), inner_ty);
                    bool()
                }
                ast::operators::UnaryOp::Neg => {
                    tc.expect_ty(inner_span, int(), inner_ty);
                    int()
                }
            };

            let ty = ty.with_ghost(is_ghost).ty(tc);

            ExprData::Unary { op, inner }.typed(ty)
        }
        ast::Expr::BlockExpr(it) => {
            let block = tc.check_block(it, |f| f);
            Expr::new_block(block)
        }
        ast::Expr::ReturnExpr(it) => {
            if let Some(expr) = it.expr() {
                let expr_span = expr.span();
                let expr_idx = check(tc, expr);

                tc.expect_ty(expr_span, tc.return_ty(), tc.expr_ty(expr_idx));

                ExprData::Return(Some(expr_idx)).typed(tc.new_free())
            } else {
                ExprData::Return(None).typed(tc.new_free())
            }
        }
        ast::Expr::BinExpr(it) => {
            let lhs = check_opt(tc, it, it.lhs());
            let (_op_token, op) = it.op_details().expect("binary op did not have details");
            let rhs = check_opt(tc, it, it.rhs());

            let lhs_ty = tc.expr_ty(lhs).tc_strip_ghost(&mut tc.typer);
            let rhs_ty = tc.expr_ty(rhs).tc_strip_ghost(&mut tc.typer);

            let is_ghost = tc.is_ghost(lhs) || tc.is_ghost(rhs);
            let ty = match op {
                BinaryOp::LogicOp(_) => {
                    tc.expect_ty(it, bool(), lhs_ty);
                    tc.expect_ty(it, bool(), rhs_ty);
                    bool()
                }
                BinaryOp::CmpOp(CmpOp::Eq { .. }) => {
                    tc.unify(it.span(), lhs_ty, rhs_ty);
                    bool()
                }
                BinaryOp::CmpOp(CmpOp::Ord { .. }) => {
                    tc.expect_ty(it, int(), lhs_ty);
                    tc.expect_ty(it, int(), rhs_ty);
                    bool()
                }
                BinaryOp::ArithOp(op) => match op {
                    ArithOp::Add => match tc.ty_data(lhs_ty) {
                        TypeData::Primitive(Primitive::Int) => {
                            tc.expect_ty(tc.expr_span(rhs), lhs_ty, rhs_ty)
                        }
                        TypeData::List(_) => tc.expect_ty(tc.expr_span(rhs), lhs_ty, rhs_ty),
                        _ => tc.push_error(
                            it,
                            None,
                            None,
                            TypeCheckErrorKind::NotYetImplemented(format!(
                                "addition of '{}' and '{}'",
                                tc.pretty_ty(lhs_ty),
                                tc.pretty_ty(rhs_ty)
                            )),
                        ),
                    },
                    ArithOp::Mul
                    | ArithOp::Sub
                    | ArithOp::Div
                    | ArithOp::Rem
                    | ArithOp::Shl
                    | ArithOp::Shr
                    | ArithOp::BitXor
                    | ArithOp::BitOr
                    | ArithOp::BitAnd => {
                        tc.expect_ty(it, int(), lhs_ty);
                        tc.expect_ty(it, int(), rhs_ty);
                        int()
                    }
                },
                BinaryOp::Assignment => {
                    let span = it.rhs().map(|rhs| rhs.span()).unwrap_or(it.span());

                    if !tc.is_ghost(lhs) && (tc.is_ghost(rhs) || tc.scope.is_ghost()) {
                        // NOTE: Assignment from ghost to non-ghost
                        tc.push_error(
                            tc.expr_span(rhs),
                            None,
                            None,
                            TypeCheckErrorKind::GhostAssignedToNonGhost,
                        );
                    }

                    tc.expect_ty(span, lhs_ty, rhs_ty)
                }
            };

            let ty = if is_ghost { ty.ghost().ty(tc) } else { ty };

            ExprData::Bin { lhs, op, rhs }.typed(ty)
        }
        ast::Expr::CallExpr(it) => {
            let fn_expr = check_inner(tc, it);
            let args: Vec<_> = it
                .arg_list()
                .unwrap()
                .args()
                .map(|arg| check_inner(tc, &arg))
                .collect();

            match tc.ty_data(tc.expr_ty(fn_expr)) {
                TypeData::Function {
                    attrs,
                    name: _,
                    params,
                    return_ty,
                } => {
                    let mut ghostify_pure = false;

                    if tc.scope.is_ghost() {
                        if !(attrs.is_ghost() || attrs.is_pure()) {
                            tc.push_error(
                                it.span(),
                                None,
                                None,
                                TypeCheckErrorKind::NonGhostNorPureCalledInGhost,
                            );
                        }

                        if attrs.is_pure() {
                            ghostify_pure = true;
                        }
                    }

                    if args.len() != params.len() {
                        tc.push_error(
                            it.expr()
                                .as_ref()
                                .map(|e| e.span())
                                .unwrap_or_else(|| it.span()),
                            None,
                            None,
                            TypeCheckErrorKind::NotYetImplemented(
                                "argument count mismatch".to_string(),
                            ),
                        );
                    }
                    for (a, b) in args.iter().zip(params.iter().map(|p| p.ty)) {
                        let b = tc.cx[b].ty;
                        let expected = b.with_ghost(ghostify_pure);
                        tc.expect_ty(tc.expr_span(*a), expected, tc.expr_ty(*a));
                    }

                    ExprData::Call {
                        expr: fn_expr,
                        args,
                    }
                    .typed(return_ty.with_ghost(ghostify_pure).ty(tc))
                }
                TypeData::Error => ExprData::Call {
                    expr: fn_expr,
                    args,
                }
                .typed(error()),
                t => todo!("`{t:?}` is not a function"),
            }
        }
        ast::Expr::RangeExpr(it) => {
            let lhs = it.lhs().map(|lhs| check(tc, lhs));
            let rhs = it.rhs().map(|rhs| check(tc, rhs));

            let ty = match (lhs, rhs) {
                (None, None) => {
                    return tc.expr_error(
                        &expr,
                        None,
                        None,
                        TypeCheckErrorKind::NotYetImplemented("inference of '..'".to_string()),
                    )
                }
                (None, Some(x)) | (Some(x), None) => {
                    let x_ty = tc.expr_ty(x);
                    let actual = x_ty.tc_strip_ghost(&mut tc.typer);
                    tc.expect_ty(tc.expr_span(x), int(), actual);
                    x_ty
                }
                (Some(lhs), Some(rhs)) => {
                    let lhs_ty = tc.expr_ty(lhs);
                    let lhs_ty_no_ghost = lhs_ty.tc_strip_ghost(&mut tc.typer);
                    let rhs_ty = tc.expr_ty(rhs);
                    let rhs_ty_no_ghost = rhs_ty.tc_strip_ghost(&mut tc.typer);
                    tc.expect_ty(tc.expr_span(lhs), int(), lhs_ty_no_ghost);
                    tc.expect_ty(tc.expr_span(rhs), int(), rhs_ty_no_ghost);
                    lhs_ty
                }
            };

            ExprData::Range { lhs, rhs }.typed(tc.ty_id(TypeData::Range(ty)))
        }
        ast::Expr::IndexExpr(it) => {
            let base = check_opt(tc, it, it.base());
            let index = check_opt(tc, it, it.index());

            let base_ty = tc.expr_ty(base);
            let index_ty = tc.expr_ty(index);

            let is_ghost =
                base_ty.tc_is_ghost(&mut tc.typer) || index_ty.tc_is_ghost(&mut tc.typer);

            let is_range = match tc.ty_data(index_ty) {
                TypeData::Primitive(Primitive::Int) => false,
                TypeData::Range(idx) => {
                    tc.expect_ty(it, int().ghost(), idx);
                    true
                }
                _ => {
                    tc.expect_ty(it, int().ghost(), index_ty);
                    false
                }
            };

            let base_ty_no_ghost = base_ty.tc_strip_ghost(&mut tc.typer);
            match tc.ty_data(base_ty_no_ghost) {
                TypeData::List(elem_ty) => {
                    if is_range {
                        ExprData::Index { base, index }.typed(base_ty.with_ghost(is_ghost).ty(tc))
                    } else {
                        ExprData::Index { base, index }.typed(elem_ty.with_ghost(is_ghost).ty(tc))
                    }
                }
                _ => {
                    return tc.expr_error(
                        &expr,
                        None,
                        None,
                        TypeCheckErrorKind::NotYetImplemented(format!(
                            "index into {}",
                            tc.pretty_ty(tc.expr_ty(base))
                        )),
                    )
                }
            }
        }
        ast::Expr::ListExpr(it) => {
            let mut elem_ty = None;
            let elems: Vec<_> = it
                .comma_exprs()
                .map(|comma_expr| {
                    let expr = check_inner(tc, &comma_expr);
                    if let Some(t) = elem_ty {
                        tc.expect_ty(comma_expr.span(), t, tc.expr_ty(expr));
                    } else {
                        elem_ty = Some(tc.expr_ty(expr));
                    }
                    expr
                })
                .collect();

            if let Some(ty) = elem_ty {
                let inner_ty_no_ghost = ty.tc_strip_ghost(&mut tc.typer);

                ExprData::List { elems }.typed(
                    tc.ty_id(TypeData::List(inner_ty_no_ghost))
                        .with_ghost(ty.tc_is_ghost(&mut tc.typer))
                        .ty(tc),
                )
            } else {
                let elem_ty = tc.new_free();
                ExprData::List { elems }.typed(tc.ty_id(TypeData::List(elem_ty)))
            }
        }
        ast::Expr::FieldExpr(it) => {
            let expr = check_inner(tc, it);
            let field = if let Some(field) = it.field() {
                Ident::from(field)
            } else {
                todo!()
            };

            let expr_ty = tc.expr_ty(expr);
            let expr_ty_no_ghost = expr_ty.tc_strip_ghost(&mut tc.typer);
            let (sf, field_ty): (Option<Field>, TypeId) = match tc.ty_data(expr_ty_no_ghost) {
                TypeData::Error => (None, error()),
                TypeData::Ref { is_mut, inner } => match tc.ty_data(inner) {
                    TypeData::Struct(s) => {
                        if let Some(field) = tc
                            .struct_fields(s)
                            .find(|f| f.name(tc.db).as_str() == field.as_str())
                        {
                            (
                                Some(field),
                                tc.expect_find_type(&field.ty(tc.db, tc.root))
                                    .with_ghost(field.is_ghost(tc.db))
                                    .ty(tc),
                            )
                        } else {
                            return tc.expr_error(
                                field.span(),
                                None,
                                None,
                                TypeCheckErrorKind::UnknownStructField {
                                    field,
                                    strukt: s.name(tc.db),
                                },
                            );
                        }
                    }
                    _ => {
                        tc.push_error(
                            it.field().map(|f| f.span()).unwrap_or_else(|| it.span()),
                            None,
                            None,
                            TypeCheckErrorKind::NotYetImplemented(format!(
                                "field of reference to something that is not a struct: {}",
                                tc.pretty_ty(inner)
                            )),
                        );
                        (None, error())
                    }
                },
                TypeData::Struct(s) => {
                    if let Some(field) = tc
                        .struct_fields(s)
                        .find(|f| f.name(tc.db).deref() == field.deref())
                    {
                        (Some(field), tc.expect_find_type(&field.ty(tc.db, tc.root)))
                    } else {
                        tc.push_error(
                            field.span(),
                            None,
                            None,
                            TypeCheckErrorKind::UnknownStructField {
                                field: field.clone(),
                                strukt: s.name(tc.db),
                            },
                        );
                        (None, error())
                    }
                }
                TypeData::List(ty) => match field.as_str() {
                    "len" => {
                        let field =
                            Field::new(tc.db, FieldParent::List(ty), field.clone(), false, None);
                        let int_ty = int();
                        let int_ty_src = tc.unsourced_ty(int_ty);
                        tc.field_tys.entry(field).or_insert(int_ty_src);
                        (Some(field), int())
                    }
                    _ => {
                        return tc.expr_error(
                            it.span(),
                            None,
                            None,
                            TypeCheckErrorKind::NotYetImplemented(format!(
                                "unknown field on list '{field}'"
                            )),
                        )
                    }
                },
                _ => {
                    return tc.expr_error(
                        it.span(),
                        None,
                        None,
                        TypeCheckErrorKind::NotYetImplemented(format!(
                            "field access with base is '{}'",
                            tc.pretty_ty(expr_ty)
                        )),
                    )
                }
            };

            ExprData::Field {
                expr,
                field_name: field,
                field: sf,
            }
            .typed(field_ty)
        }
        ast::Expr::NotNullExpr(it) => {
            let inner = check_inner(tc, it);

            let inner_ty = tc.expr_ty(inner).tc_strip_ghost(&mut tc.typer);

            let ty = match tc.ty_data(inner_ty) {
                TypeData::Optional(inner_ty) => inner_ty
                    .with_ghost(tc.expr_ty(inner).tc_is_ghost(&mut tc.typer))
                    .ty(tc),
                _ => {
                    return tc.expr_error(
                        it.span(),
                        None,
                        None,
                        TypeCheckErrorKind::NotYetImplemented(format!(
                            "`!` on non-nullable type '{}'",
                            tc.pretty_ty(tc.expr_ty(inner))
                        )),
                    )
                }
            };

            ExprData::NotNull(inner).typed(ty)
        }
        ast::Expr::StructExpr(it) => {
            let name: Ident = if let Some(name) = it.name() {
                name.into()
            } else {
                todo!()
            };
            let struct_ty = tc.find_named_type(name.clone());

            let s = match tc.ty_data(struct_ty) {
                TypeData::Struct(s) => s,
                _ => {
                    let expr_err = tc.expr_error(
                        name.span(),
                        None,
                        None,
                        TypeCheckErrorKind::UnknownStruct { name },
                    );

                    // NOTE: Still check the types of the fields
                    for f in it.fields() {
                        let _ = check_inner(tc, &f);
                    }

                    return expr_err;
                }
            };

            let fields = tc.struct_fields(s).collect_vec();
            let mut present_fields = vec![];

            for f in it.fields() {
                let mut matched = false;
                for sf in &fields {
                    let field_name = Ident::from(f.name().unwrap());
                    if field_name.as_str() == sf.name(tc.db).as_str() {
                        let value = check_inner(tc, &f);
                        let expected = tc.expect_find_type(&sf.ty(tc.db, tc.root));
                        tc.expect_ty(tc.expr_span(value), expected, tc.expr_ty(value));
                        present_fields.push(StructExprField::new(*sf, field_name, value));
                        matched = true;
                    }
                }
                if !matched {
                    tc.push_error(
                        f.span(),
                        None,
                        None,
                        TypeCheckErrorKind::NotYetImplemented(format!(
                            "field '{}' does not exist on '{}'",
                            f.name().unwrap(),
                            s.name(tc.db)
                        )),
                    );
                }
            }

            Expr {
                ty: struct_ty,
                data: ExprData::Struct {
                    struct_declaration: s,
                    struct_span: name.span(),
                    fields: present_fields,
                },
            }
        }
        ast::Expr::ParenExpr(e) => return check_inner(tc, e),
        ast::Expr::RefExpr(it) => {
            let expr = check_inner(tc, it);
            let is_mut = it.mut_token().is_some();
            let inner = tc.expr_ty(expr).ty(tc).tc_strip_ghost(&mut tc.typer);

            let ty = tc
                .ty_id(TypeData::Ref { is_mut, inner })
                .with_ghost(tc.expr_ty(expr).ty(tc).tc_is_ghost(&mut tc.typer))
                .ty(tc);

            ExprData::Ref { is_mut, expr }.typed(ty)
        }
        ast::Expr::IdentExpr(it) => {
            let name = if let Some(name) = it.name() {
                name
            } else {
                todo!()
            };

            if name.self_token().is_some() {
                let ty = if let Some(self_ty) = tc.self_ty() {
                    self_ty
                } else {
                    tc.push_error(
                        name.span(),
                        None,
                        None,
                        TypeCheckErrorKind::UndefinedVariable(name.to_string()),
                    )
                };

                ExprData::Self_.typed(ty)
            } else {
                let var = tc.lookup_name(&name);
                let ty = tc.var_ty(var);

                ExprData::Ident(VariableRef::new(var, name.span())).typed(ty)
            }
        }
        ast::Expr::NullExpr(_) => ExprData::Literal(Literal::Null).typed(null()),
        ast::Expr::ResultExpr(_) => {
            // TODO: Perhaps this should be an error, as commented out below
            // let ty = if let Some(return_ty) = tc.return_ty() {
            //     return_ty
            // } else {
            //     tc.push_error(
            //         expr.span(),
            //         None,
            //         None,
            //         TypeCheckErrorKind::ResultWithNoReturn,
            //     )
            // };
            let ty = tc.return_ty();
            ExprData::Result.typed(ty)
        }
        ast::Expr::QuantifierExpr(it) => {
            let quantifier = match it.quantifier() {
                Some(q) if q.forall_token().is_some() => Quantifier::Forall,
                Some(q) if q.exists_token().is_some() => Quantifier::Exists,
                None => todo!(),
                _ => todo!(),
            };
            let params = tc.check_param_list(it.param_list());

            tc.push_scope(|f| f);
            let params = params
                .into_iter()
                .map(|param| {
                    let var = tc.declare_variable(
                        VariableDeclaration::new_param(param.name.clone()),
                        param.ty,
                        // TODO: Should this not be the ty?
                        param.name.span(),
                    );
                    Param {
                        is_ghost: true,
                        name: var,
                        ty: param.ty,
                    }
                })
                .collect();

            let expr = check_inner(tc, it);
            tc.pop_scope();

            ExprData::Quantifier {
                quantifier,
                params,
                expr,
            }
            .typed(bool())
        }
    };

    let new = if tc.scope.is_ghost() {
        Expr {
            ty: new.ty.ghost().ty(tc),
            data: new.data,
        }
    } else {
        new
    };

    tc.alloc_expr(new, &expr)
}

fn check_if_expr(tc: &mut TypeChecker, if_expr: ast::IfExpr) -> ExprIdx {
    let condition = tc.check(&if_expr, if_expr.condition());

    let condition_ty = tc.expr_ty(condition);
    let is_ghost = condition_ty.tc_is_ghost(&mut tc.typer);
    if is_ghost {
        tc.expect_ty(
            if_expr
                .condition()
                .map(|e| e.span())
                .unwrap_or_else(|| if_expr.span()),
            ghost_bool(),
            condition_ty,
        );
    } else {
        tc.expect_ty(
            if_expr
                .condition()
                .map(|e| e.span())
                .unwrap_or_else(|| if_expr.span()),
            bool(),
            condition_ty,
        );
    }

    let (then_branch, then_ty) = if let Some(then_branch) = if_expr.then_branch() {
        let block = tc.check_block(&then_branch, |f| {
            if is_ghost {
                f | ScopeFlags::GHOST
            } else {
                f
            }
        });
        let ty = block.return_ty;
        (
            tc.alloc_expr(Expr::new_block(block), then_branch.span()),
            ty,
        )
    } else {
        todo!()
    };
    let (else_branch, else_tail_span) = if_expr
        .else_branch()
        .map(|else_branch| match else_branch {
            ast::IfExprElse::IfExpr(e) => (check_if_expr(tc, e), None),
            ast::IfExprElse::BlockExpr(b) => {
                let block =
                    tc.check_block(&b, |f| if is_ghost { f | ScopeFlags::GHOST } else { f });
                let tail_span = block
                    .tail_expr
                    .map(|e| tc.expr_span(e))
                    .or_else(|| block.stmts.last().map(|s| s.span));
                let expr = tc.alloc_expr(Expr::new_block(block), b.span());
                (expr, tail_span)
            }
        })
        .unzip();
    // TODO: tail_span should perhaps be a general concept for exprs, to
    // provide better spans in more cases
    let else_tail_span = else_tail_span.flatten();

    let ty = if let Some(b) = else_branch {
        let span = else_tail_span.unwrap_or_else(|| if_expr.span());
        let then_ty = then_ty.with_ghost(is_ghost);
        tc.unify(span, then_ty, tc.expr_ty(b))
    } else {
        let else_ty = void().with_ghost(is_ghost);
        tc.expect_ty(&if_expr, then_ty, else_ty)
    };

    let result = IfExpr {
        if_span: if_expr.if_token().unwrap().span(),
        is_ghost,
        return_ty: ty,
        condition,
        then_branch,
        else_branch,
    };
    tc.alloc_expr(Expr::new_if(result), if_expr.span())
}