use std::cmp::Ordering;

use mist_core::hir::{self, Block, ExprIdx, ItemContext, Program, Quantifier, Type, TypeData};
use mist_syntax::ast::operators::{ArithOp, BinaryOp, CmpOp, LogicOp};
use silvers::{
    expression::{
        AbstractLocalVar, AccessPredicate, BinOp, Exp, FieldAccess, LocalVar, LocationAccess,
        PermExp, PredicateAccess, PredicateAccessPredicate, QuantifierExp, ResourceAccess,
    },
    program::{Field, Function, LocalVarDecl, Predicate},
    statement::{Seqn, Stmt},
    typ::Type as SType,
};
use tracing::error;

#[salsa::tracked]
pub fn viper_file(db: &dyn crate::Db, program: hir::Program) -> silvers::program::Program {
    let mut fields = vec![];
    let mut predicates = vec![];
    let mut methods = vec![];
    let mut functions = vec![];

    for item in program.items(db) {
        let Some(item) = hir::item(db, program, item.clone()) else { continue };
        match item {
            hir::Item::Type(ty_decl) => match ty_decl.data(db) {
                hir::TypeDeclData::Struct(s) => {
                    let lowering = ViperLowering {
                        db,
                        cx: ItemContext::default(),
                        program,
                        return_variable: None,
                    };
                    predicates.push(Predicate {
                        name: s.name(db).to_string(),
                        formal_args: vec![LocalVarDecl {
                            name: "this".to_string(),
                            typ: SType::ref_(),
                        }],
                        body: None,
                    });
                    for field in hir::struct_fields(db, program, s) {
                        let ty = lowering.lower_ty(field.ty);
                        fields.push(Field {
                            name: field.name.to_string(),
                            typ: ty.ty,
                        })
                    }
                }
            },
            hir::Item::TypeInvariant(_) => {}
            hir::Item::Function(function) => {
                let Some((cx, source_map)) = hir::item_lower(db, program, item) else { continue };
                match viper_function(db, program, function, cx) {
                    ViperFunction::Function(it) => functions.push(it),
                    ViperFunction::Method(it) => methods.push(it),
                }
            }
        }
    }

    silvers::program::Program {
        domains: vec![],
        fields,
        functions,
        predicates,
        methods,
        extensions: vec![],
    }
}

#[salsa::tracked]
pub fn viper_function(
    db: &dyn crate::Db,
    program: hir::Program,
    function: hir::Function,
    cx: ItemContext,
) -> ViperFunction {
    let is_pure = function.attrs(db).is_pure();

    let mut pres = vec![];
    let mut posts = vec![];

    let (lowering, return_targets, formal_returns) = if let Some(ret) = function.ret(db) {
        if is_pure {
            let lowering = ViperLowering {
                db,
                cx: cx.clone(),
                program,
                return_variable: None,
            };

            let ty_constraints = lowering.lower_input_param(
                ret,
                LowerTypeFlags {
                    name: "result".to_string(),
                    explicit_perms: PermExp::Full,
                    is_reference: false,
                    optional: false,
                },
            );

            posts.extend_from_slice(&ty_constraints.preconditions);
            posts.extend_from_slice(&ty_constraints.postconditions);

            (
                lowering,
                Some(AbstractLocalVar::Result {
                    typ: ty_constraints.ty,
                }),
                vec![],
            )
        } else {
            let ret_name = "returned_value".to_string();

            let lowering = ViperLowering {
                db,
                cx: cx.clone(),
                program,
                return_variable: None,
            };
            let ty_constraints = lowering.lower_input_param(
                ret,
                LowerTypeFlags {
                    name: ret_name.to_string(),
                    explicit_perms: PermExp::Full,
                    is_reference: false,
                    optional: false,
                },
            );
            let lowering = ViperLowering {
                db,
                cx: cx.clone(),
                program,
                return_variable: Some(LocalVar::new(
                    ret_name.to_string(),
                    ty_constraints.ty.clone(),
                )),
            };

            posts.extend_from_slice(&ty_constraints.preconditions);
            posts.extend_from_slice(&ty_constraints.postconditions);

            (
                lowering,
                Some(AbstractLocalVar::LocalVar(LocalVar::new(
                    ret_name.to_string(),
                    ty_constraints.ty.clone(),
                ))),
                vec![LocalVarDecl {
                    name: ret_name,
                    typ: ty_constraints.ty,
                }],
            )
        }
    } else {
        let lowering = ViperLowering {
            db,
            cx: cx.clone(),
            program,
            return_variable: None,
        };
        (lowering, None, vec![])
    };

    let formal_args = function
        .param_list(db)
        .params
        .iter()
        .map(|param| {
            let ty_constraints = lowering.lower_input_param(
                param.ty,
                LowerTypeFlags {
                    name: param.name.to_string(),
                    explicit_perms: PermExp::Full,
                    is_reference: false,
                    optional: false,
                },
            );

            pres.extend_from_slice(&ty_constraints.preconditions);
            posts.extend_from_slice(&ty_constraints.postconditions);

            LocalVarDecl {
                name: param.name.to_string(),
                typ: ty_constraints.ty,
            }
        })
        .collect();

    for condition in lowering.cx.conditions() {
        match condition {
            hir::Condition::Requires(it) => {
                for &expr in it {
                    let (pre, lowered_expr) = lowering.lower_expr(Default::default(), expr);
                    if !pre.is_empty() {
                        error!("{expr:?} produced a pre statements: {pre:?}")
                    }
                    if let Some(expr) = lowered_expr {
                        pres.push(expr);
                    } else {
                        error!("{expr:?} produced no expression")
                    }
                }
            }
            hir::Condition::Ensures(it) => {
                for &expr in it {
                    let (post, lowered_expr) = lowering.lower_expr(Default::default(), expr);
                    if !post.is_empty() {
                        error!("{expr:?} produced a post statements: {post:?}")
                    }
                    if let Some(expr) = lowered_expr {
                        posts.push(expr);
                    } else {
                        error!("{expr:?} produced no expression")
                    }
                }
            }
        }
    }

    if is_pure {
        let typ = lowering
            .lower_ty(
                function
                    .ret(db)
                    .unwrap_or_else(|| Type::new(db, TypeData::Error, None)),
            )
            .ty;
        let body = if let Some(body_expr) = cx.body_expr() {
            let lowering = ViperLowering { cx, ..lowering };
            let (pre_stmts, body) = lowering.lower_expr(LowerExprFlags::default(), body_expr);
            body
        } else {
            None
        };

        ViperFunction::Function(Function {
            name: function.name(db).to_string(),
            formal_args,
            typ,
            pres,
            posts,
            body,
        })
    } else {
        let body = if let Some(body_expr) = cx.body_expr() {
            let lowering = ViperLowering { cx, ..lowering };
            let (pre_stmts, body) = lowering.lower_expr(LowerExprFlags::default(), body_expr);
            // TODO
            None
        } else {
            None
        };

        let method = silvers::program::Method {
            name: function.name(db).to_string(),
            formal_args,
            formal_returns,
            pres,
            posts,
            body,
        };
        ViperFunction::Method(method)
    }
}

#[derive(Debug, Clone)]
pub enum FinalValuePlacement {
    LocalVar(LocalVar),
    Field(FieldAccess),
    Expression,
}

#[derive(Debug, Default, Clone)]
pub struct LowerExprFlags {
    final_value_placement: Option<FinalValuePlacement>,
}

impl LowerExprFlags {
    fn with_final_value_placement(
        &self,
        final_value_placement: Option<FinalValuePlacement>,
    ) -> Self {
        LowerExprFlags {
            final_value_placement,
            // ..self.clone()
        }
    }
}

struct ViperLowering<'w> {
    db: &'w dyn crate::Db,
    program: Program,
    cx: ItemContext,
    return_variable: Option<LocalVar>,
}

#[derive(Debug)]
pub struct TypeWithConstraint {
    ty: SType,
    preconditions: Vec<Exp>,
    postconditions: Vec<Exp>,
}

#[derive(Debug, Clone)]
pub struct LowerTypeFlags {
    pub name: String,
    pub explicit_perms: PermExp,
    pub is_reference: bool,
    pub optional: bool,
}

impl ViperLowering<'_> {
    pub fn lower_expr(&self, flags: LowerExprFlags, expr: ExprIdx) -> (Vec<Stmt>, Option<Exp>) {
        match &self.cx[expr].data {
            hir::ExprData::Literal(it) => match it {
                hir::Literal::Null => (vec![], Some(Exp::null())),
                hir::Literal::Int(val) => (vec![], Some(Exp::int(*val))),
                hir::Literal::Bool(val) => (vec![], Some(Exp::boolean(*val))),
            },
            hir::ExprData::Result => {
                if let Some(var) = self.return_variable.clone() {
                    (
                        vec![],
                        Some(Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(var))),
                    )
                } else {
                    // TODO
                    let typ = SType::internal_type();
                    (
                        vec![],
                        Some(Exp::AbstractLocalVar(AbstractLocalVar::Result { typ })),
                    )
                }
            }
            hir::ExprData::Ident(it) => (
                vec![],
                Some(Exp::AbstractLocalVar(
                    silvers::expression::AbstractLocalVar::LocalVar(LocalVar::new(
                        self.cx.var_ident(it).to_string(),
                        self.lower_ty(self.cx.var_ty(*it)).ty,
                    )),
                )),
            ),
            hir::ExprData::Field {
                expr, field_name, ..
            } => {
                let (rcr_stmts, rcr) =
                    self.lower_expr(flags.with_final_value_placement(None), *expr);
                (
                    rcr_stmts,
                    Some(Exp::LocationAccess(ResourceAccess::Location(
                        LocationAccess::Field(FieldAccess {
                            rcr: Box::new(rcr.unwrap_or_else(Exp::null)),
                            field: Field {
                                name: field_name.to_string(),
                                // TODO
                                typ: SType::ref_(),
                            },
                        }),
                    ))),
                )
            }
            hir::ExprData::Struct {
                struct_declaration,
                fields,
                ..
            } => {
                let mut stmts = vec![];

                let (initializer_stmts, target) =
                    self.initialize_target(self.cx[expr].ty, flags.final_value_placement);
                stmts.extend_from_slice(&initializer_stmts);
                let rcr = match target {
                    FinalValuePlacement::LocalVar(lhs) => {
                        stmts.push(Stmt::NewStmt {
                            lhs: lhs.clone(),
                            fields: hir::struct_fields(self.db, self.program, *struct_declaration)
                                .iter()
                                .map(|f| Field::new(f.name.to_string(), self.lower_ty(f.ty).ty))
                                .collect(),
                        });
                        Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(lhs))
                    }
                    FinalValuePlacement::Field(_) => todo!(),
                    FinalValuePlacement::Expression => todo!(),
                };

                for f in fields {
                    let (pre_stmts, expr) = self.lower_expr(LowerExprFlags::default(), f.value);
                    stmts.extend_from_slice(&pre_stmts);
                    stmts.push(Stmt::FieldAssign {
                        lhs: FieldAccess {
                            rcr: Box::new(rcr.clone()),
                            // TODO: Use proper type
                            field: Field::new(f.name.to_string(), SType::ref_()),
                        },
                        rhs: expr.unwrap_or_else(Exp::null),
                    });
                }

                (stmts, Some(rcr))
            }
            hir::ExprData::Missing => (vec![], None),
            hir::ExprData::If(it) => {
                let (mut stmts, condition) = self.lower_expr(flags.clone(), it.condition);
                let then_stmts = self.lower_block(flags.clone(), it.then_branch.clone());
                let else_stmts = if let Some(else_branch) = &it.else_branch {
                    match else_branch.as_ref() {
                        hir::Else::If(_) => todo!(),
                        hir::Else::Block(block) => self.lower_block(flags.clone(), block.clone()),
                    }
                } else {
                    Seqn {
                        ss: vec![],
                        scoped_seqn_declarations: vec![],
                    }
                };

                let condition = if let Some(cond) = condition {
                    cond
                } else {
                    tracing::error!("if-statement had no condition");
                    return (stmts, None);
                };

                match &flags.final_value_placement {
                    Some(p) => match p {
                        FinalValuePlacement::LocalVar(_) => {
                            error!("final_value_placement: {:?} {:?} {:?}", p, stmts, flags);
                            (vec![], None)
                        }
                        FinalValuePlacement::Field(_) => {
                            error!("final_value_placement: {:?} {:?} {:?}", p, stmts, flags);
                            (vec![], None)
                        }
                        FinalValuePlacement::Expression => match it.else_branch.as_deref() {
                            Some(hir::Else::If(_)) => todo!(),
                            Some(hir::Else::Block(else_block)) => (
                                stmts,
                                Some(Exp::Cond {
                                    cond: Box::new(condition),
                                    thn: Box::new(self.lower_block_to_expr(
                                        flags.clone(),
                                        it.then_branch.clone(),
                                    )),
                                    els: Box::new(
                                        self.lower_block_to_expr(flags, else_block.clone()),
                                    ),
                                }),
                            ),
                            None => (
                                stmts,
                                Some(condition.implies(
                                    self.lower_block_to_expr(flags.clone(), it.then_branch.clone()),
                                )),
                            ),
                        },
                    },
                    None => {
                        stmts.push(Stmt::If {
                            cond: condition,
                            thn: then_stmts,
                            els: else_stmts,
                        });

                        (stmts, None)
                    }
                }
            }
            hir::ExprData::Block(block) => {
                (vec![], Some(self.lower_block_to_expr(flags, block.clone())))
            }
            hir::ExprData::Call { expr, args } => {
                let funcname = match &self.cx[*expr].data {
                    hir::ExprData::Ident(var) => self.cx.var_ident(var).to_string(),
                    _ => todo!(),
                };

                let mut stmts = vec![];

                let args = args
                    .iter()
                    .filter_map(|arg| {
                        let (pre_stmts, a) =
                            self.lower_expr(flags.with_final_value_placement(None), *arg);
                        stmts.extend_from_slice(&pre_stmts);
                        if let Some(a) = a {
                            Some(Box::new(a))
                        } else {
                            error!("{:?} did not produce any expression", &self.cx[*arg]);
                            None
                        }
                    })
                    .collect();

                (stmts, Some(Exp::FuncApp { funcname, args }))
            }
            &hir::ExprData::Unary { op, inner } => {
                // TODO
                self.lower_expr(flags, inner)
            }
            &hir::ExprData::Bin { lhs, op, rhs } => {
                let mut stmts = vec![];

                let (lhs_stmts, lhs) = self.lower_expr(flags.with_final_value_placement(None), lhs);
                let lhs = lhs.unwrap_or_else(|| {
                    error!("no lhs of expression");
                    Exp::null()
                });
                stmts.extend_from_slice(&lhs_stmts);
                let (rhs_stmts, rhs) = self.lower_expr(flags.with_final_value_placement(None), rhs);
                let rhs = rhs.unwrap_or_else(Exp::null);
                stmts.extend_from_slice(&rhs_stmts);

                use BinOp::*;

                (
                    stmts.clone(),
                    Some(Exp::Bin {
                        op: match op {
                            BinaryOp::LogicOp(op) => match op {
                                LogicOp::Or => Or,
                                LogicOp::And => And,
                            },
                            BinaryOp::CmpOp(op) => match op {
                                CmpOp::Eq { negated: true } => NeCmp,
                                CmpOp::Eq { negated: false } => EqCmp,
                                CmpOp::Ord { ordering, strict } => match (ordering, strict) {
                                    (Ordering::Less, true) => LtCmp,
                                    (Ordering::Less, false) => LeCmp,
                                    (Ordering::Equal, true) => EqCmp,
                                    (Ordering::Equal, false) => EqCmp,
                                    (Ordering::Greater, true) => GtCmp,
                                    (Ordering::Greater, false) => GeCmp,
                                },
                            },
                            BinaryOp::ArithOp(op) => match op {
                                ArithOp::Add => Add,
                                ArithOp::Mul => Mul,
                                ArithOp::Sub => Sub,
                                ArithOp::Div => Div,
                                ArithOp::Rem => Mod,
                                ArithOp::Shl
                                | ArithOp::Shr
                                | ArithOp::BitXor
                                | ArithOp::BitOr
                                | ArithOp::BitAnd => todo!(),
                            },
                            BinaryOp::Assignment => {
                                let stmt = match lhs {
                                    Exp::LocationAccess(ResourceAccess::Location(
                                        LocationAccess::Field(lhs),
                                    )) => Stmt::FieldAssign { lhs, rhs },
                                    Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(lhs)) => {
                                        Stmt::LocalVarAssign { lhs, rhs }
                                    }
                                    Exp::AbstractLocalVar(AbstractLocalVar::Result { typ }) => {
                                        todo!()
                                    }
                                    _ => todo!(),
                                };
                                stmts.push(stmt);
                                return (stmts, None);
                            }
                        },
                        left: Box::new(lhs),
                        right: Box::new(rhs),
                    }),
                )
            }
            hir::ExprData::Range { lhs, rhs } => {
                // TODO
                (vec![], None)
            }
            hir::ExprData::Index { base, index } => {
                let (mut pre_stmts, base) = self.lower_expr(flags.clone(), *base);
                let (index_pre_stmts, index) = self.lower_expr(flags, *index);

                pre_stmts.extend_from_slice(&index_pre_stmts);

                (
                    pre_stmts,
                    base.and_then(|base| {
                        Some(Exp::Seq(silvers::expression::SeqExp::Index {
                            s: Box::new(base),
                            idx: Box::new(index?),
                        }))
                    }),
                )
            }
            hir::ExprData::List { elems } => {
                let mut stmts = vec![];

                let elems = elems
                    .iter()
                    .filter_map(|arg| {
                        let (pre_stmts, a) =
                            self.lower_expr(flags.with_final_value_placement(None), *arg);
                        stmts.extend_from_slice(&pre_stmts);
                        if let Some(a) = a {
                            Some(Box::new(a))
                        } else {
                            error!("{:?} did not produce any expression", &self.cx[*arg]);
                            None
                        }
                    })
                    .collect();

                (
                    stmts,
                    Some(Exp::Seq(silvers::expression::SeqExp::Explicit { elems })),
                )
            }
            hir::ExprData::Ref { is_mut, expr } => self.lower_expr(flags, *expr),
            hir::ExprData::Quantifier {
                quantifier,
                params,
                expr,
            } => {
                let variables = params
                    .params
                    .iter()
                    .map(|p| LocalVarDecl::new(p.name.to_string(), self.lower_ty(p.ty).ty))
                    .collect();
                let triggers = vec![];
                let (pre_stmts, exp) = self.lower_expr(
                    flags.with_final_value_placement(Some(FinalValuePlacement::Expression)),
                    *expr,
                );
                let exp = if let Some(exp) = exp {
                    Box::new(exp)
                } else {
                    tracing::error!(
                        "quantifier did not have any expression: {}",
                        self.cx.pretty_expr(self.db, *expr)
                    );
                    return (vec![], None);
                };
                let quantifier = match quantifier {
                    Quantifier::Forall => QuantifierExp::Forall {
                        variables,
                        triggers,
                        exp,
                    },
                    Quantifier::Exists => QuantifierExp::Exists {
                        variables,
                        triggers,
                        exp,
                    },
                };
                (pre_stmts, Some(Exp::Quantifier(quantifier)))
            }
        }
    }

    fn initialize_target(
        &self,
        ty: Type,
        final_value_placement: Option<FinalValuePlacement>,
    ) -> (Vec<Stmt>, FinalValuePlacement) {
        if let Some(final_value_placement) = final_value_placement {
            (vec![], final_value_placement)
        } else {
            let ty_constraints = self.lower_ty(ty);
            let var = LocalVar::new("unique_name_123".to_string(), ty_constraints.ty);
            (
                vec![Stmt::LocalVarDeclStmt {
                    decl: silvers::program::LocalVarDecl {
                        name: var.name.to_string(),
                        typ: var.typ.clone(),
                    },
                }],
                FinalValuePlacement::LocalVar(var),
            )
        }
    }

    pub fn lower_block_to_expr(&self, flags: LowerExprFlags, block: Block) -> Exp {
        dbg!(&block);

        match block.stmts.len() {
            0 => {
                if let Some(tail) = block.tail_expr {
                    let (stmts, expr) = self.lower_expr(flags, tail);
                    if !stmts.is_empty() {
                        tracing::error!("lower_block_to_expr tail-expr had stmts");
                    }
                    if let Some(expr) = expr {
                        expr
                    } else {
                        tracing::error!("lower_block_to_expr tail-expr produced no expr");
                        Exp::null()
                    }
                } else {
                    tracing::error!("lower_block_to_expr not yet implemented for empty blocks without tail-expr");
                    Exp::null()
                }
            }
            1 => match &block.stmts[0].data {
                hir::StatementData::Return(_) => todo!(),
                hir::StatementData::Expr(expr) => {
                    let (stmts, expr) = self.lower_expr(flags, *expr);
                    if !stmts.is_empty() {
                        tracing::error!("lower_block_to_expr stmt expr had stmts");
                    }
                    if let Some(expr) = expr {
                        expr
                    } else {
                        tracing::error!("lower_block_to_expr stmt expr produced no expr");
                        Exp::null()
                    }
                }
                hir::StatementData::Let {
                    variable,
                    explicit_ty: _,
                    initializer,
                } => {
                    tracing::error!("lower_block_to_expr of let stmt");
                    Exp::null()
                }
                hir::StatementData::While {
                    expr,
                    invariants,
                    decreases: _,
                    body,
                } => todo!(),
                hir::StatementData::Assertion { kind, exprs } => todo!(),
            },
            _ => {
                tracing::error!("lower_block_to_expr not yet implemented");
                Exp::null()
            }
        }
    }

    pub fn lower_block(&self, flags: LowerExprFlags, block: Block) -> Seqn {
        let stmts = block
            .stmts
            .iter()
            .flat_map(|stmt| match &stmt.data {
                hir::StatementData::Return(Some(it)) => {
                    let (mut stmts, expr) = self.lower_expr(flags.clone(), *it);
                    if let Some(ret_var) = self.return_variable.clone() {
                        if let Some(expr) = expr {
                            stmts.push(Stmt::LocalVarAssign {
                                lhs: ret_var,
                                rhs: expr,
                            });
                        } else {
                            error!("Failed to produce expression used in return");
                        };
                        stmts.push(Stmt::Assume {
                            exp: Exp::boolean(false),
                        });
                    } else {
                        stmts.push(Stmt::Assume {
                            exp: Exp::boolean(false),
                        });
                    }
                    stmts
                }
                hir::StatementData::Return(None) => {
                    vec![Stmt::Assume {
                        exp: Exp::boolean(false),
                    }]
                }
                hir::StatementData::Expr(it) => {
                    let (mut stmts, expr) = self.lower_expr(flags.clone(), *it);
                    if let Some(expr) = expr {
                        stmts.push(Stmt::Expression(expr));
                    }
                    stmts
                }
                &hir::StatementData::Let {
                    variable,
                    explicit_ty: _,
                    initializer,
                } => {
                    let (mut stmts, expr) = self.lower_expr(
                        flags.with_final_value_placement(Some(FinalValuePlacement::LocalVar(
                            LocalVar::new(
                                self.cx.var_ident(variable).to_string(),
                                self.lower_ty(self.cx.var_ty(variable)).ty,
                            ),
                        ))),
                        initializer,
                    );

                    let ty_constraints = self.lower_ty(self.cx.var_ty(variable));
                    let lhs = LocalVarDecl::new(
                        self.cx.var_ident(variable).to_string(),
                        ty_constraints.ty,
                    );
                    stmts.insert(0, Stmt::LocalVarDeclStmt { decl: lhs.clone() });

                    if let Some(expr) = expr {
                        stmts.push(Stmt::LocalVarAssign {
                            lhs: LocalVar::new(lhs.name, lhs.typ),
                            rhs: expr,
                        })
                    }

                    stmts
                }
                hir::StatementData::While {
                    expr,
                    invariants,
                    decreases: _,
                    body,
                } => {
                    let (pre_expr, expr) = self.lower_expr(LowerExprFlags::default(), *expr);
                    if !pre_expr.is_empty() {
                        return vec![];
                    }
                    let invs = invariants
                        .iter()
                        .flat_map(|inv| {
                            inv.iter().flat_map(|inv| {
                                let (pre_stmts, expr) =
                                    self.lower_expr(LowerExprFlags::default(), *inv);

                                if !pre_stmts.is_empty() {
                                    return None;
                                }

                                expr
                            })
                        })
                        .collect();

                    let body = self.lower_block(LowerExprFlags::default(), body.clone());

                    vec![Stmt::While {
                        cond: expr.unwrap_or_else(Exp::null),
                        invs,
                        body,
                    }]
                }
                hir::StatementData::Assertion { kind, exprs } => {
                    let mut stmts = vec![];

                    for expr in exprs {
                        let (ss, exp) = self.lower_expr(Default::default(), *expr);
                        stmts.extend_from_slice(&ss);
                        let exp = exp.unwrap_or_else(|| {
                            error!("expression of assertion did not produce an expression");
                            Exp::null()
                        });
                        match kind {
                            hir::AssertionKind::Assert => stmts.push(Stmt::Assert { exp }),
                            hir::AssertionKind::Assume => todo!(),
                            hir::AssertionKind::Inhale => todo!(),
                            hir::AssertionKind::Exhale => todo!(),
                        }
                    }

                    stmts
                }
            })
            .collect();

        Seqn {
            ss: stmts,
            scoped_seqn_declarations: vec![],
        }
    }

    pub fn lower_input_param(&self, ty: hir::Type, flags: LowerTypeFlags) -> TypeWithConstraint {
        match ty.data(self.db) {
            TypeData::Error => TypeWithConstraint {
                ty: SType::Atomic(silvers::typ::AtomicType::InternalType),
                preconditions: vec![],
                postconditions: vec![],
            },
            TypeData::Void => todo!(),
            &TypeData::Ref { is_mut, inner } => {
                let perms = if is_mut {
                    PermExp::Full
                } else {
                    // TODO: This should be a new explicit ghost param
                    PermExp::Wildcard
                };

                self.lower_input_param(
                    inner,
                    LowerTypeFlags {
                        explicit_perms: perms,
                        is_reference: true,
                        ..flags
                    },
                )
            }
            &TypeData::Ghost(inner) => self.lower_input_param(inner, flags),
            &TypeData::List(inner) => {
                let t = self.lower_input_param(inner, flags);
                TypeWithConstraint {
                    ty: SType::Seq {
                        element_type: Box::new(t.ty),
                    },
                    ..t
                }
            }
            &TypeData::Range(inner) => {
                let t = self.lower_input_param(inner, flags);
                TypeWithConstraint {
                    ty: SType::internal_type(),
                    ..t
                }
            }
            TypeData::Optional(inner) => self.lower_input_param(
                *inner,
                LowerTypeFlags {
                    optional: true,
                    ..flags
                },
            ),
            TypeData::Primitive(it) => {
                let ty = match it {
                    hir::Primitive::Int => SType::Atomic(silvers::typ::AtomicType::Int),
                    hir::Primitive::Bool => SType::Atomic(silvers::typ::AtomicType::Bool),
                };
                TypeWithConstraint {
                    ty,
                    preconditions: vec![],
                    postconditions: vec![],
                }
            }
            TypeData::Struct(s) => {
                let arg = Box::new(Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(
                    LocalVar::new(flags.name.to_string(), SType::ref_()),
                )));

                let predicate =
                    Exp::AccessPredicate(AccessPredicate::Predicate(PredicateAccessPredicate {
                        loc: PredicateAccess {
                            args: vec![arg.clone()],
                            predicate_name: s.name(self.db).to_string(),
                        },
                        perm: Box::new(Exp::Perm(flags.explicit_perms)),
                    }));

                let predicate = if flags.optional {
                    arg.ne_cmp(Exp::null()).implies(predicate)
                } else {
                    predicate
                };

                TypeWithConstraint {
                    ty: SType::ref_(),
                    preconditions: vec![predicate.clone()],
                    postconditions: if flags.is_reference {
                        vec![predicate]
                    } else {
                        vec![]
                    },
                }
            }
            TypeData::Null => todo!(),
            TypeData::Function {
                attrs,
                name: _,
                params,
                return_ty,
            } => todo!(),
        }
    }

    pub fn lower_ty(&self, ty: Type) -> TypeWithConstraint {
        match ty.data(self.db) {
            TypeData::Error => TypeWithConstraint {
                ty: SType::Atomic(silvers::typ::AtomicType::InternalType),
                preconditions: vec![],
                postconditions: vec![],
            },
            TypeData::Void => TypeWithConstraint {
                ty: SType::Atomic(silvers::typ::AtomicType::InternalType),
                preconditions: vec![],
                postconditions: vec![],
            },
            TypeData::Ref { is_mut: _, inner } => self.lower_ty(*inner),
            TypeData::Ghost(inner) => self.lower_ty(*inner),
            TypeData::List(inner) => {
                let t = self.lower_ty(*inner);
                TypeWithConstraint {
                    ty: SType::Seq {
                        element_type: Box::new(t.ty),
                    },
                    ..t
                }
            }
            TypeData::Range(inner) => {
                let t = self.lower_ty(*inner);
                TypeWithConstraint {
                    ty: SType::internal_type(),
                    ..t
                }
            }
            TypeData::Optional(inner) => self.lower_ty(*inner),
            TypeData::Primitive(it) => {
                let ty = match it {
                    hir::Primitive::Int => SType::int(),
                    hir::Primitive::Bool => SType::bool(),
                };

                TypeWithConstraint {
                    ty,
                    preconditions: vec![],
                    postconditions: vec![],
                }
            }
            TypeData::Struct(s) => TypeWithConstraint {
                ty: SType::ref_(),
                preconditions: vec![Exp::FuncApp {
                    funcname: s.name(self.db).to_string(),
                    args: vec![Box::new(Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(
                        LocalVar::new("some_name".to_string(), SType::ref_()),
                    )))],
                }],
                postconditions: vec![],
            },
            TypeData::Null => todo!(),
            TypeData::Function {
                attrs,
                name: _,
                params,
                return_ty,
            } => TypeWithConstraint {
                ty: SType::internal_type(),
                preconditions: vec![],
                postconditions: vec![],
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ViperFunction {
    Function(silvers::program::Function),
    Method(silvers::program::Method),
}
