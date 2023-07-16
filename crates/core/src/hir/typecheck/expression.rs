use itertools::{
    Either::{self, Left, Right},
    Itertools,
};
use mist_syntax::{
    ast::{
        self,
        operators::{ArithOp, BinaryOp, CmpOp},
        HasAttrs, HasExpr, HasName, Spanned,
    },
    SourceSpan,
};
use tracing::warn;

use crate::{
    def::Name,
    hir::{
        Expr, ExprData, ExprIdx, ForExpr, IfExpr, Literal, Quantifier, QuantifierOver,
        SpanOrAstPtr, StructExprField, WhileExpr,
    },
    types::{
        primitive::{bool, error, ghost_bool, ghost_int, int, void},
        BuiltinField, BuiltinKind, Field, GenericArgs, Primitive, TypeData, TypeId, TypeProvider,
        TDK,
    },
    VariableDeclaration,
};

use super::{
    NamedType, ScopeFlags, TypeCheckErrorKind, TypeChecker, Typed, TypingMut, TypingMutExt,
};

pub(super) fn check_opt(
    tc: &mut TypeChecker,
    fallback_span: impl Spanned,
    expr: Option<ast::Expr>,
) -> ExprIdx {
    if let Some(expr) = expr {
        check(tc, expr)
    } else {
        tc.expr_error(fallback_span.span(), None, None, TypeCheckErrorKind::MissingExpression)
    }
}
pub(super) fn check_inner(tc: &mut TypeChecker, expr: &impl HasExpr) -> ExprIdx {
    if let Some(expr) = expr.expr() {
        check(tc, expr)
    } else {
        tc.expr_error(expr.span(), None, None, TypeCheckErrorKind::MissingExpression)
    }
}
pub(super) fn check_lhs(tc: &mut TypeChecker, expr: ast::Expr) -> ExprIdx {
    match &expr {
        ast::Expr::IndexExpr(_)
        | ast::Expr::NotNullExpr(_)
        | ast::Expr::FieldExpr(_)
        | ast::Expr::IdentExpr(_) => {
            check_impl(tc, expr.clone()).map_right(|new| tc.alloc_expr(new, &expr)).either_into()
        }
        ast::Expr::ParenExpr(it) => {
            if let Some(inner) = it.expr() {
                check_impl(tc, inner).map_right(|new| tc.alloc_expr(new, &expr)).either_into()
            } else {
                tc.expr_error(&expr, None, None, TypeCheckErrorKind::MissingLhs)
            }
        }

        ast::Expr::RefExpr(_)
        | ast::Expr::Literal(_)
        | ast::Expr::IfExpr(_)
        | ast::Expr::ReturnExpr(_)
        | ast::Expr::WhileExpr(_)
        | ast::Expr::ForExpr(_)
        | ast::Expr::PrefixExpr(_)
        | ast::Expr::BinExpr(_)
        | ast::Expr::BlockExpr(_)
        | ast::Expr::RangeExpr(_)
        | ast::Expr::CallExpr(_)
        | ast::Expr::ListExpr(_)
        | ast::Expr::StructExpr(_)
        | ast::Expr::NullExpr(_)
        | ast::Expr::ResultExpr(_)
        | ast::Expr::QuantifierExpr(_) => {
            tc.ty_error(expr.span(), None, None, TypeCheckErrorKind::InvalidLhsOfAssignment);
            check(tc, expr)
        }
    }
}
pub(super) fn check(tc: &mut TypeChecker, expr: ast::Expr) -> ExprIdx {
    check_impl(tc, expr.clone())
        .map_right(|new| {
            let new = if tc.scope.is_ghost() {
                Expr { ty: new.ty.ghosted(tc), data: new.data }
            } else {
                new
            };

            tc.alloc_expr(new, &expr)
        })
        .either_into()
}
fn check_impl(tc: &mut TypeChecker, expr: ast::Expr) -> Either<ExprIdx, Expr> {
    Right(match &expr {
        ast::Expr::Literal(it) => match it.kind() {
            ast::LiteralKind::IntNumber(s) => {
                ExprData::Literal(Literal::Int(s.to_string().parse().unwrap())).typed(int())
            }
            ast::LiteralKind::Bool(b) => ExprData::Literal(Literal::Bool(b)).typed(bool()),
        },
        ast::Expr::IfExpr(it) => return Left(check_if_expr(tc, it.clone())),
        ast::Expr::WhileExpr(it) => {
            let expr = check_opt(tc, it, it.expr());
            let invariants =
                it.invariants().map(|inv| tc.check_boolean_exprs(inv.comma_exprs())).collect();
            let decreases = tc.check_decreases(it.decreases());
            let body = check_block(tc, it.span(), tc.is_ghost(expr), it.block_expr());
            ExprData::While(WhileExpr { expr, invariants, decreases, body }).typed(void())
        }
        ast::Expr::ForExpr(it) => {
            let variable = if let Some(name) = it.name() {
                let ty = tc.unsourced_ty(int());
                let span = name.span();
                tc.declare_variable(VariableDeclaration::new_let(name, false), ty, span)
            } else {
                return Left(tc.expr_error(
                    expr.span().set_len(0),
                    None,
                    None,
                    TypeCheckErrorKind::NotYetImplemented("for-loop without variable".to_string()),
                ));
            };

            let in_expr = check_opt(tc, it.span(), it.expr());
            let in_expr_ty = tc.expr_ty(in_expr).strip_ghost(tc);
            let in_ty = tc.alloc_ty_data(TypeData::range(tc.db, int()));
            tc.expect_ty((it.expr().as_ref(), it.span()), in_ty, in_expr_ty);

            let invariants =
                it.invariants().map(|inv| tc.check_boolean_exprs(inv.comma_exprs())).collect();

            let body = check_block(tc, it.span(), tc.is_ghost(in_expr), it.block_expr());

            ExprData::For(ForExpr {
                is_ghost: tc.is_ghost(in_expr),
                variable,
                in_expr,
                invariants,
                body,
            })
            .typed(void())
        }
        ast::Expr::PrefixExpr(it) => {
            let (_op_token, op) =
                if let Some(op) = it.op_details() { op } else { todo!("{it:#?}") };
            let inner = check_inner(tc, it);
            let inner_span = tc.expr_span(inner);
            let inner_ty = tc.expr_ty(inner).strip_ghost(tc);

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
                ast::operators::UnaryOp::RangeMin | ast::operators::UnaryOp::RangeMax => {
                    let range_over = tc.new_free();
                    let range_ty = tc.alloc_ty_data(TypeData::range(tc.db, range_over));
                    tc.expect_ty(inner_span, range_ty, inner_ty);
                    range_over
                }
            };

            let ty = ty.with_ghost(tc, is_ghost);

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
            let (_op_token, op) = it.op_details().expect("binary op did not have details");

            if let BinaryOp::Assignment = op {
                let lhs = if let Some(lhs) = it.lhs() {
                    check_lhs(tc, lhs)
                } else {
                    tc.expr_error(&expr, None, None, TypeCheckErrorKind::MissingLhs)
                };
                let rhs = check_opt(tc, it.span(), it.rhs());

                if !tc.is_ghost(lhs) && (tc.is_ghost(rhs) || tc.scope.is_ghost()) {
                    // NOTE: Assignment from ghost to non-ghost
                    tc.ty_error(
                        tc.expr_span(rhs),
                        None,
                        None,
                        TypeCheckErrorKind::GhostAssignedToNonGhost,
                    );
                }

                let span = it.rhs().map(|rhs| rhs.span()).unwrap_or(it.span());

                let lhs_ty = tc.expr_ty(lhs).strip_ghost(tc);
                let rhs_ty = tc.expr_ty(rhs).strip_ghost(tc);
                tc.expect_ty(span, lhs_ty, rhs_ty);

                return Left(tc.alloc_expr(
                    ExprData::Bin { lhs, op: BinaryOp::Assignment, rhs }.typed(void()),
                    &expr,
                ));
            }

            let lhs = check_opt(tc, it, it.lhs());
            let rhs = check_opt(tc, it, it.rhs());

            let lhs_ty = tc.expr_ty(lhs).strip_ghost(tc);
            let rhs_ty = tc.expr_ty(rhs).strip_ghost(tc);

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
                    ArithOp::Add => match tc.ty_kind(lhs_ty) {
                        TDK::Primitive(Primitive::Int) => {
                            tc.expect_ty(tc.expr_span(rhs), lhs_ty, rhs_ty)
                        }
                        TDK::Builtin(BuiltinKind::List, _) => {
                            tc.expect_ty(tc.expr_span(rhs), lhs_ty, rhs_ty)
                        }
                        _ => tc.ty_error(
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
                BinaryOp::Assignment => unreachable!(),
            };

            let ty = if is_ghost { ty.ghosted(tc) } else { ty };

            ExprData::Bin { lhs, op, rhs }.typed(ty)
        }
        ast::Expr::CallExpr(it) => {
            let fn_expr = check_inner(tc, it);
            let args: Vec<_> =
                it.arg_list().unwrap().args().map(|arg| check_inner(tc, &arg)).collect();

            match tc.ty_kind(tc.expr_ty(fn_expr)) {
                TDK::Function { attrs, name: _, params, return_ty } => {
                    let mut ghostify_pure = false;

                    if tc.scope.is_ghost() {
                        if !(attrs.is_ghost() || attrs.is_pure()) {
                            type_error(tc, &expr, TypeCheckErrorKind::NonGhostNorPureCalledInGhost);
                        }

                        if attrs.is_pure() {
                            ghostify_pure = true;
                        }
                    }

                    if args.len() != params.len() {
                        type_error(
                            tc,
                            it.expr().as_ref().map(|e| e.span()).unwrap_or_else(|| it.span()),
                            TypeCheckErrorKind::NotYetImplemented(
                                "argument count mismatch".to_string(),
                            ),
                        );
                    }
                    for (a, b) in args
                        .iter()
                        .zip(params.iter().map(|p| p.ty.with_ghost(tc, p.is_ghost)).collect_vec())
                    {
                        let expected = b.with_ghost(tc, ghostify_pure).ty(tc.db);
                        tc.expect_ty(tc.expr_span(*a), expected, tc.expr_ty(*a));
                    }

                    ExprData::Call { expr: fn_expr, args }
                        .typed(return_ty.with_ghost(tc, ghostify_pure))
                }
                TDK::Error => ExprData::Call { expr: fn_expr, args }.typed(error()),
                t => todo!("`{t:?}` is not a function"),
            }
        }
        ast::Expr::RangeExpr(it) => {
            let lhs = it.lhs().map(|lhs| check(tc, lhs));
            let rhs = it.rhs().map(|rhs| check(tc, rhs));

            let ty = match (lhs, rhs) {
                (None, None) => {
                    return Left(expr_error(
                        tc,
                        &expr,
                        TypeCheckErrorKind::NotYetImplemented("inference of '..'".to_string()),
                    ));
                }
                (None, Some(x)) | (Some(x), None) => {
                    let x_ty = tc.expr_ty(x);
                    tc.expect_ty(tc.expr_span(x), ghost_int(), x_ty);
                    x_ty
                }
                (Some(lhs), Some(rhs)) => {
                    let lhs_ty = tc.expr_ty(lhs).strip_ghost(tc);
                    let rhs_ty = tc.expr_ty(rhs).strip_ghost(tc);
                    tc.expect_ty(tc.expr_span(lhs), ghost_int(), lhs_ty);
                    tc.expect_ty(tc.expr_span(rhs), ghost_int(), rhs_ty);
                    lhs_ty
                }
            };

            ExprData::Range { lhs, rhs }.typed(tc.alloc_ty_data(TypeData::range(tc.db, ty)))
        }
        ast::Expr::IndexExpr(it) => {
            let base = check_opt(tc, it, it.base());
            let index = check_opt(tc, it, it.index());

            let base_ty = tc.expr_ty(base);
            let index_ty = tc.expr_ty(index);

            let is_ghost = base_ty.is_ghost(tc) || index_ty.is_ghost(tc);

            let is_range = match tc.ty_kind(index_ty) {
                TDK::Primitive(Primitive::Int) => false,
                TDK::Builtin(BuiltinKind::Range, gargs) => {
                    let idx = gargs.get(tc.db, 0);
                    tc.expect_ty(it, ghost_int(), idx);
                    true
                }
                _ => {
                    tc.expect_ty(it, ghost_int(), index_ty);
                    false
                }
            };

            match tc.ty_kind(base_ty) {
                TDK::Builtin(BuiltinKind::List, gargs) => {
                    let elem_ty = gargs.get(tc.db, 0);
                    if is_range {
                        ExprData::Index { base, index }.typed(base_ty.with_ghost(tc, is_ghost))
                    } else {
                        ExprData::Index { base, index }.typed(elem_ty.with_ghost(tc, is_ghost))
                    }
                }
                _ => {
                    return Left(expr_error(
                        tc,
                        &expr,
                        TypeCheckErrorKind::NotYetImplemented(format!(
                            "index into {}",
                            tc.pretty_ty(tc.expr_ty(base))
                        )),
                    ))
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
                        tc.expect_ty(&comma_expr, t, tc.expr_ty(expr));
                    } else {
                        elem_ty = Some(tc.expr_ty(expr));
                    }
                    expr
                })
                .collect();

            if let Some(ty) = elem_ty {
                let inner_ty_no_ghost = ty.strip_ghost(tc);

                ExprData::List { elems }.typed(
                    tc.alloc_ty_data(TypeData::list(tc.db, inner_ty_no_ghost))
                        .with_ghost(tc, ty.is_ghost(tc)),
                )
            } else {
                let elem_ty = tc.new_free();
                ExprData::List { elems }.typed(tc.alloc_ty_data(TypeData::list(tc.db, elem_ty)))
            }
        }
        ast::Expr::FieldExpr(it) => {
            let expr = check_inner(tc, it);
            let (field_ast, field) = if let Some(field_ast) = it.field() {
                let field = Name::from(&field_ast);
                (field_ast, field)
            } else {
                return Right(Expr { ty: error(), data: ExprData::Missing });
            };

            let expr_ty = tc.expr_ty(expr);
            let (sf, field_ty): (Option<Field>, TypeId) = match tc.ty_kind(expr_ty) {
                TDK::Error => (None, error()),
                // TODO: potentially use `is_mut`
                TDK::Ref { is_mut: _, inner } => match tc.ty_kind(inner) {
                    TDK::Adt(s) => {
                        if let Some(field) =
                            tc.fields_of(s).into_iter().find(|f| f.name(tc.db) == field)
                        {
                            (
                                Some(field.into()),
                                tc.field_ty(field.into()).with_ghost(tc, field.is_ghost(tc.db)),
                            )
                        } else {
                            return Left(expr_error(
                                tc,
                                field_ast.span(),
                                TypeCheckErrorKind::UnknownStructField {
                                    field,
                                    strukt: s.name(tc.db),
                                },
                            ));
                        }
                    }
                    _ => {
                        type_error(
                            tc,
                            it.field().map(|f| f.span()).unwrap_or_else(|| it.span()),
                            TypeCheckErrorKind::NotYetImplemented(format!(
                                "field of reference to something that is not a struct: {}",
                                tc.pretty_ty(inner)
                            )),
                        );
                        (None, error())
                    }
                },
                TDK::Adt(s) => {
                    // NOTE: Query the ADT to give it a chance to finish initialization
                    tc.adt_ty(s);
                    if let Some(field) =
                        tc.fields_of(s).into_iter().find(|f| f.name(tc.db) == field)
                    {
                        (Some(field.into()), tc.field_ty(field.into()))
                    } else {
                        tc.ty_error(
                            &field_ast,
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
                TDK::Builtin(kind, _) => {
                    match BuiltinField::try_create(tc, expr_ty, kind, field.as_str()) {
                        Some(bf) => (Some(Field::Builtin(bf)), bf.ty(tc)),
                        None => {
                            return Left(expr_error(
                                tc,
                                it.span(),
                                TypeCheckErrorKind::NotYetImplemented(format!(
                                    "unknown field on {} '{field}'",
                                    kind.name()
                                )),
                            ));
                        }
                    }
                }
                _ => {
                    return Left(expr_error(
                        tc,
                        it.span(),
                        TypeCheckErrorKind::NotYetImplemented(format!(
                            "field access with base is '{}'",
                            tc.pretty_ty(expr_ty)
                        )),
                    ));
                }
            };

            let field_ty = field_ty.with_ghost(tc, expr_ty.is_ghost(tc));

            ExprData::Field { expr, field: sf.unwrap_or(Field::Undefined) }.typed(field_ty)
        }
        ast::Expr::NotNullExpr(it) => {
            let inner = check_inner(tc, it);

            let ty = match tc.ty_kind(tc.expr_ty(inner)) {
                TDK::Optional(inner_ty) => inner_ty.with_ghost(tc, tc.expr_ty(inner).is_ghost(tc)),
                _ => {
                    return Left(expr_error(
                        tc,
                        it.span(),
                        TypeCheckErrorKind::NotYetImplemented(format!(
                            "`!` on non-nullable type '{}'",
                            tc.pretty_ty(tc.expr_ty(inner))
                        )),
                    ));
                }
            };

            ExprData::NotNull(inner).typed(ty)
        }
        ast::Expr::StructExpr(it) => {
            let name_ref = if let Some(name_ref) = it.name_ref() { name_ref } else { todo!() };
            let named_type = tc.find_named_type(&name_ref, (&name_ref).into());
            let adt = match named_type {
                Ok(NamedType::AdtKind(kind)) => {
                    let generic_args = GenericArgs::new(
                        tc.db,
                        (0..kind.arity(tc.db)).map(|_| tc.new_free()).collect(),
                    );
                    tc.instantiate_adt(kind, generic_args)
                }
                Ok(NamedType::Builtin(_)) | Ok(NamedType::TypeId(_)) | Err(_) => {
                    // NOTE: Still check the types of the fields
                    for f in it.fields() {
                        let _ = check_inner(tc, &f);
                    }

                    return Left(expr_error(
                        tc,
                        name_ref.span(),
                        TypeCheckErrorKind::UnknownStruct { name: name_ref.into() },
                    ));
                }
            };

            let fields = tc.fields_of(adt);
            let mut present_fields = vec![];

            for expr_f in it.fields() {
                let mut matched = false;
                for &field in &fields {
                    let field_name = Name::from(&expr_f.name_ref().unwrap());
                    if field_name == field.name(tc.db) {
                        let value = check_inner(tc, &expr_f);
                        let expected = tc.field_ty(field.into());
                        tc.expect_ty(tc.expr_span(value), expected, tc.expr_ty(value));
                        present_fields.push(StructExprField::new(field, value));
                        matched = true;
                    }
                }
                if !matched {
                    tc.ty_error(
                        expr_f.span(),
                        None,
                        None,
                        TypeCheckErrorKind::NotYetImplemented(format!(
                            "field '{}' does not exist on '{}'",
                            expr_f.name_ref().unwrap(),
                            adt.name(tc.db)
                        )),
                    );
                }
            }

            Expr { ty: tc.adt_ty(adt), data: ExprData::Adt { adt, fields: present_fields } }
        }
        ast::Expr::ParenExpr(e) => return Left(check_inner(tc, e)),
        ast::Expr::RefExpr(it) => {
            let expr = check_inner(tc, it);
            let is_mut = it.mut_token().is_some();
            let inner = tc.expr_ty(expr).strip_ghost(tc);

            let ty = tc
                .alloc_ty_data(TDK::Ref { is_mut, inner }.into())
                .with_ghost(tc, tc.expr_ty(expr).is_ghost(tc));

            ExprData::Ref { is_mut, expr }.typed(ty)
        }
        ast::Expr::IdentExpr(it) => {
            let name = if let Some(name) = it.name_ref() { name } else { todo!() };

            if name.self_token().is_some() {
                let ty = if let Some(self_ty) = tc.self_ty() {
                    self_ty
                } else {
                    tc.ty_error(
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

                ExprData::Ident(var).typed(ty)
            }
        }
        ast::Expr::NullExpr(_) => ExprData::Literal(Literal::Null).typed(tc.new_null()),
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
            tc.push_scope(|f| f);

            let over = match it.quantifier_over() {
                Some(ast::QuantifierOver::ParamList(param_list)) => QuantifierOver::Vars(
                    param_list
                        .params()
                        .map(|p| {
                            let name = if let Some(name) = p.name() { name } else { todo!() };
                            let ty = if let Some(ty) = p.ty() {
                                tc.lower_type(&ty)
                            } else {
                                let t = tc.new_free();
                                tc.unsourced_ty(t)
                            }
                            .with_ghost(tc, p.is_ghost());

                            let var_decl = VariableDeclaration::new_param(name.clone());
                            let ty_src: SpanOrAstPtr<_> =
                                p.ty().as_ref().map(|t| t.into()).unwrap_or(name.span().into());
                            tc.declare_variable(var_decl, ty, ty_src)
                        })
                        .collect(),
                ),
                Some(ast::QuantifierOver::NameInExprs(it)) => {
                    let ins = it
                        .name_in_exprs()
                        .map(|it| {
                            let ty = tc.new_free();
                            let ty = tc.unsourced_ty(ty);
                            let name = it.name().unwrap();
                            let name_span = name.span();
                            let var_decl = tc.declare_variable(
                                VariableDeclaration::new_let(name, false),
                                ty,
                                name_span,
                            );
                            let over_expr = check_opt(tc, it.span(), it.expr());

                            let range_ty = match tc.ty_kind(tc.expr_ty(over_expr)) {
                                TDK::Builtin(BuiltinKind::Range, _) => tc.alloc_ty_data(
                                    TypeData::range(tc.db, ty.ty(tc.db)).kind.ghost(),
                                ),
                                TDK::Builtin(BuiltinKind::Set, _) => tc
                                    .alloc_ty_data(TypeData::set(tc.db, ty.ty(tc.db)).kind.ghost()),
                                // Fallback
                                _ => tc.alloc_ty_data(
                                    TypeData::range(tc.db, ty.ty(tc.db)).kind.ghost(),
                                ),
                            };

                            tc.expect_ty(
                                (it.expr().as_ref(), name_span),
                                range_ty,
                                tc.expr_ty(over_expr),
                            );

                            (var_decl, over_expr)
                        })
                        .collect();

                    QuantifierOver::In(ins)
                }
                None => {
                    warn!("quantifier does not quantify over anything");
                    QuantifierOver::Vars(vec![])
                }
            };

            let expr = check_inner(tc, it);
            tc.pop_scope();

            ExprData::Quantifier { quantifier, over, expr }.typed(bool())
        }
    })
}

fn check_block(
    tc: &mut TypeChecker,
    span: impl Into<SpanOrAstPtr<ast::Expr>>,
    is_ghost: bool,
    b: Option<ast::BlockExpr>,
) -> ExprIdx {
    if let Some(b) = b {
        let block = tc.check_block(&b, |f| if is_ghost { f | ScopeFlags::GHOST } else { f });
        tc.alloc_expr(Expr::new_block(block), b.span())
    } else {
        expr_error(tc, span, TypeCheckErrorKind::NotYetImplemented("empty block".to_string()))
    }
}

fn check_if_expr(tc: &mut TypeChecker, if_expr: ast::IfExpr) -> ExprIdx {
    let condition = tc.check(&if_expr, if_expr.condition());

    let condition_ty = tc.expr_ty(condition);
    let is_ghost = condition_ty.is_ghost(tc);
    if is_ghost {
        tc.expect_ty((if_expr.condition().as_ref(), &if_expr), ghost_bool(), condition_ty);
    } else {
        tc.expect_ty((if_expr.condition().as_ref(), if_expr.span()), bool(), condition_ty);
    }

    let then_branch = check_block(tc, if_expr.span(), is_ghost, if_expr.then_branch());
    let then_ty = tc.expr_ty(then_branch);
    let (else_tail_span, else_branch) = if_expr
        .else_branch()
        .map(|else_branch| match else_branch {
            ast::IfExprElse::IfExpr(e) => (e.span(), check_if_expr(tc, e)),
            ast::IfExprElse::BlockExpr(b) => {
                let block =
                    tc.check_block(&b, |f| if is_ghost { f | ScopeFlags::GHOST } else { f });
                let tail_span = Spanned::span((
                    block.tail_expr.map(|e| tc.expr_span(e)),
                    block.stmts.last().and_then(|s| tc.source_map.stmt_ast(*s).map(|it| it.span())),
                    b.span(),
                ));
                (tail_span, tc.alloc_expr(Expr::new_block(block), b.span()))
            }
        })
        .or_else(|| {
            tc.ty_data(then_ty).is_bool().then(|| {
                let span_end = if_expr.span().end();
                let span = SourceSpan::new_start_end(span_end, span_end);
                (span, tc.alloc_expr(ExprData::Literal(Literal::Bool(true)).typed(bool()), span))
            })
        })
        .unzip();
    // TODO: tail_span should perhaps be a general concept for exprs, to
    // provide better spans in more cases

    let ty = if let Some(b) = else_branch {
        let span = else_tail_span.unwrap_or_else(|| if_expr.span());
        let then_ty = then_ty.with_ghost(tc, is_ghost);
        eprintln!(
            "if {} else {} ({})",
            tc.pretty_ty(then_ty),
            tc.pretty_ty(tc.expr_ty(b)),
            tc.cx.pretty_expr(tc.db, b)
        );
        tc.unify(span, then_ty, tc.expr_ty(b))
    } else {
        let else_ty = void().with_ghost(tc, is_ghost);
        tc.expect_ty(&if_expr, then_ty, else_ty)
    };

    let result = IfExpr { is_ghost, return_ty: ty, condition, then_branch, else_branch };
    tc.alloc_expr(Expr::new_if(result), if_expr.span())
}

fn type_error(tc: &mut TypeChecker, span: impl Spanned, kind: TypeCheckErrorKind) -> TypeId {
    tc.ty_error(span, None, None, kind)
}
fn expr_error(
    tc: &mut TypeChecker,
    span: impl Into<SpanOrAstPtr<ast::Expr>>,
    kind: TypeCheckErrorKind,
) -> ExprIdx {
    tc.expr_error(span, None, None, kind)
}
