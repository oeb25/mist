use std::collections::HashMap;

use itertools::Itertools;
use la_arena::{Arena, ArenaMap, Idx};
use miette::Diagnostic;
use mist_syntax::{
    ast::{
        operators::{ArithOp, BinaryOp, CmpOp},
        Spanned,
    },
    SourceSpan,
};
use salsa::DebugWithDb;
use thiserror::Error;

use crate::ir::{
    self, AssertionKind, Block, Else, Expr, ExprData, ExprIdx, IfExpr, Literal, Param, ParamList,
    Primitive, Program, Quantifier, Statement, StatementData, StructExprField, StructField, Type,
    TypeData, Variable, VariableId,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionContext {
    declarations: Trace<Variable, mist_syntax::ast::Name>,
    types: ArenaMap<Idx<Variable>, Type>,
    trace: Trace<Expr, Option<mist_syntax::ast::Expr>>,
}

impl std::ops::Index<ExprIdx> for FunctionContext {
    type Output = Expr;

    fn index(&self, index: ExprIdx) -> &Self::Output {
        &self.trace.arena[index]
    }
}
impl std::ops::Index<Idx<Variable>> for FunctionContext {
    type Output = Variable;

    fn index(&self, index: Idx<Variable>) -> &Self::Output {
        &self.declarations.arena[index]
    }
}
impl FunctionContext {
    pub fn var_ty(&self, var: Idx<Variable>) -> Type {
        self.types[var]
    }
}

impl Type {
    pub fn error(db: &dyn crate::Db) -> Self {
        Type::new(db, TypeData::Error)
    }
    pub fn void(db: &dyn crate::Db) -> Self {
        Type::new(db, TypeData::Void)
    }
    pub fn primitive(db: &dyn crate::Db, primitive: Primitive) -> Self {
        Type::new(db, TypeData::Primitive(primitive))
    }
    pub fn int(db: &dyn crate::Db) -> Self {
        Self::primitive(db, Primitive::Int)
    }
    pub fn bool(db: &dyn crate::Db) -> Self {
        Self::primitive(db, Primitive::Bool)
    }
}

pub struct TypeCheckExpr<'w> {
    db: &'w dyn crate::Db,
    program: Program,
    return_ty: Option<Type>,
    scope: HashMap<String, Idx<Variable>>,
    scope_stack: Vec<HashMap<String, Idx<Variable>>>,
    declarations: Trace<Variable, mist_syntax::ast::Name>,
    types: ArenaMap<Idx<Variable>, Type>,
    trace: Trace<Expr, Option<mist_syntax::ast::Expr>>,
}

impl From<TypeCheckExpr<'_>> for FunctionContext {
    fn from(value: TypeCheckExpr<'_>) -> Self {
        FunctionContext {
            declarations: value.declarations,
            types: value.types,
            trace: value.trace,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Trace<T, V> {
    arena: Arena<T>,
    map: ArenaMap<Idx<T>, V>,
}

impl<T, V> Trace<T, V> {
    pub fn new() -> Self {
        Trace {
            arena: Default::default(),
            map: Default::default(),
        }
    }

    pub fn alloc(&mut self, value: V, data: T) -> Idx<T> {
        let id = self.arena.alloc(data);
        self.map.insert(id, value);
        id
    }
}

impl<'a> TypeCheckExpr<'a> {
    pub fn new(
        db: &'a dyn crate::Db,
        program: Program,
        return_ty: Option<Type>,
    ) -> TypeCheckExpr<'a> {
        Self {
            db,
            program,
            return_ty,
            declarations: Trace::new(),
            types: ArenaMap::new(),
            scope: Default::default(),
            scope_stack: vec![],
            trace: Trace::new(),
        }
    }
    fn push_scope(&mut self) {
        self.scope_stack.push(self.scope.clone());
    }
    fn pop_scope(&mut self) {
        self.scope = self
            .scope_stack
            .pop()
            .expect("tried to pop scope while none was pushed");
    }
    fn check_if_expr(
        &mut self,
        source: &mist_syntax::ast::Expr,
        if_expr: mist_syntax::ast::IfExpr,
    ) -> ExprIdx {
        let condition = self.check(if_expr.span(), if_expr.condition());
        let then_branch = if let Some(then_branch) = if_expr.then_branch() {
            self.check_block(then_branch)
        } else {
            todo!()
        };
        let else_branch = if_expr.else_branch().map(|else_branch| match else_branch {
            mist_syntax::ast::IfExprElse::IfExpr(e) => {
                Else::If(todo!("{:?}", self.check_if_expr(source, e)))
            }
            mist_syntax::ast::IfExprElse::Block(b) => Else::Block(self.check_block(b)),
        });

        let ty = if let Some(b) = &else_branch {
            self.unify(if_expr.span(), then_branch.return_ty, b.return_ty(self.db))
        } else {
            self.expect_ty(
                if_expr.span(),
                Type::new(self.db, TypeData::Void),
                then_branch.return_ty,
            )
        };

        let expr = Expr::new(
            ty,
            ExprData::If(IfExpr {
                return_ty: ty,
                condition,
                then_branch,
                else_branch: else_branch.map(Box::new),
            }),
        );
        self.trace.alloc(Some(source.clone()), expr)
    }
    pub fn expr_ty(&self, expr: ExprIdx) -> Type {
        self.trace.arena[expr].ty
    }
    pub fn check(
        &mut self,
        fallback_span: SourceSpan,
        expr: Option<mist_syntax::ast::Expr>,
    ) -> ExprIdx {
        let expr = if let Some(expr) = expr {
            expr
        } else {
            return self.expr_error(
                fallback_span,
                None,
                None,
                TypeCheckErrorKind::MissingExpression,
            );
        };

        let new = match &expr {
            mist_syntax::ast::Expr::Literal(it) => match it.kind() {
                mist_syntax::ast::LiteralKind::IntNumber(s) => Expr::new(
                    Type::int(self.db),
                    ExprData::Literal(Literal::Int(s.to_string().parse().unwrap())),
                ),
                mist_syntax::ast::LiteralKind::Bool(b) => {
                    Expr::new(Type::bool(self.db), ExprData::Literal(Literal::Bool(b)))
                }
            },
            mist_syntax::ast::Expr::IfExpr(it) => return self.check_if_expr(&expr, it.clone()),
            mist_syntax::ast::Expr::WhileExpr(_) => todo!(),
            mist_syntax::ast::Expr::BinExpr(it) => {
                let lhs = self.check(it.span(), it.lhs());
                let (op_token, op) = if let Some(op) = it.op_details() {
                    op
                } else {
                    todo!()
                };
                let rhs = self.check(it.span(), it.rhs());

                let ty = match op {
                    BinaryOp::LogicOp(_) => {
                        self.expect_ty(it.span(), Type::bool(self.db), self.expr_ty(lhs));
                        self.expect_ty(it.span(), Type::bool(self.db), self.expr_ty(rhs));
                        Type::bool(self.db)
                    }
                    BinaryOp::CmpOp(CmpOp::Eq { .. }) => {
                        self.unify(it.span(), self.expr_ty(lhs), self.expr_ty(rhs));
                        Type::bool(self.db)
                    }
                    BinaryOp::CmpOp(CmpOp::Ord { .. }) => {
                        self.expect_ty(it.span(), Type::int(self.db), self.expr_ty(lhs));
                        self.expect_ty(it.span(), Type::int(self.db), self.expr_ty(rhs));
                        Type::bool(self.db)
                    }
                    BinaryOp::ArithOp(op) => match op {
                        ArithOp::Add
                        | ArithOp::Mul
                        | ArithOp::Sub
                        | ArithOp::Div
                        | ArithOp::Rem
                        | ArithOp::Shl
                        | ArithOp::Shr
                        | ArithOp::BitXor
                        | ArithOp::BitOr
                        | ArithOp::BitAnd => {
                            self.unify(it.span(), self.expr_ty(lhs), Type::int(self.db));
                            self.unify(it.span(), self.expr_ty(rhs), Type::int(self.db));
                            Type::new(self.db, TypeData::Primitive(Primitive::Int))
                        }
                    },
                    BinaryOp::Assignment => {
                        let span = it.rhs().map(|rhs| rhs.span()).unwrap_or(it.span());
                        self.expect_ty(span, self.expr_ty(lhs), self.expr_ty(rhs))
                    }
                };

                Expr::new(ty, ExprData::Bin { lhs, op, rhs })
            }
            mist_syntax::ast::Expr::CallExpr(it) => {
                let fn_expr = self.check(it.span(), it.expr());
                let args: Vec<_> = it
                    .arg_list()
                    .unwrap()
                    .args()
                    .map(|arg| self.check(arg.span(), arg.expr()))
                    .collect();

                match self.trace.arena[fn_expr].ty.data(self.db) {
                    TypeData::Function { params, return_ty } => {
                        if args.len() != params.len() {
                            todo!()
                        }
                        for (a, b) in args.iter().zip(params) {
                            self.expect_ty(
                                self.trace.map[*a].as_ref().unwrap().span(),
                                *b,
                                self.trace.arena[*a].ty,
                            );
                        }
                        Expr {
                            ty: *return_ty,
                            data: ExprData::Call {
                                expr: fn_expr,
                                args,
                            },
                        }
                    }
                    TypeData::Error => Expr {
                        ty: Type::error(self.db),
                        data: ExprData::Call {
                            expr: fn_expr,
                            args,
                        },
                    },
                    t => todo!("`{t:?}` is not a function"),
                }
            }
            mist_syntax::ast::Expr::IndexExpr(_) => todo!(),
            mist_syntax::ast::Expr::FieldExpr(it) => {
                let expr = self.check(it.span(), it.expr());
                let field = if let Some(field) = it.field() {
                    field
                } else {
                    todo!()
                };

                let ty = match self.trace.arena[expr].ty.data(self.db) {
                    TypeData::Error => Type::error(self.db),
                    TypeData::Ref { is_mut, inner } => {
                        let inner = inner.data(self.db);

                        match inner {
                            TypeData::Struct(s) => {
                                let fields = self.struct_fields(*s);
                                if let Some(field) = fields.iter().find(|f| f.name == field) {
                                    field.ty
                                } else {
                                    self.push_error(
                                        field.span(),
                                        None,
                                        None,
                                        TypeCheckErrorKind::UnknownStructField {
                                            field: field.to_string(),
                                            strukt: ir::struct_name(self.db, *s).to_string(),
                                        },
                                    )
                                }
                            }
                            _ => todo!(),
                        }
                    }
                    TypeData::Struct(s) => {
                        let fields = self.struct_fields(*s);
                        if let Some(field) = fields.iter().find(|f| f.name == field) {
                            field.ty
                        } else {
                            self.push_error(
                                field.span(),
                                None,
                                None,
                                TypeCheckErrorKind::UnknownStructField {
                                    field: field.to_string(),
                                    strukt: ir::struct_name(self.db, *s).to_string(),
                                },
                            )
                        }
                    }
                    _ => todo!(),
                };

                Expr::new(
                    ty,
                    ExprData::Field {
                        expr,
                        field: field.to_string(),
                    },
                )
            }
            mist_syntax::ast::Expr::StructExpr(it) => {
                let name = if let Some(name) = it.name() {
                    name
                } else {
                    todo!()
                };
                let struct_ty = self.find_named_type(name);

                let s = match struct_ty.data(self.db) {
                    TypeData::Struct(s) => *s,
                    _ => todo!(),
                };

                let fields = self.struct_fields(s);
                let mut present_fields = vec![];

                for f in it.fields() {
                    for sf in &fields {
                        let field_name = f.name().unwrap();
                        if field_name == sf.name {
                            let value = self.check(f.span(), f.expr());
                            present_fields
                                .push(StructExprField::new(field_name.to_string(), value));
                        }
                    }
                }

                Expr {
                    ty: struct_ty,
                    data: ExprData::Struct {
                        strukt: s,
                        fields: present_fields,
                    },
                }
            }
            mist_syntax::ast::Expr::ParenExpr(e) => return self.check(fallback_span, e.expr()),
            mist_syntax::ast::Expr::RefExpr(it) => {
                let expr = self.check(it.span(), it.expr());
                let is_mut = it.mut_token().is_some();
                let inner = self.trace.arena[expr].ty;

                let ty = Type::new(self.db, TypeData::Ref { is_mut, inner });

                Expr::new(ty, ExprData::Ref { is_mut, expr })
            }
            mist_syntax::ast::Expr::IdentExpr(it) => {
                let name = if let Some(name) = it.name() {
                    name
                } else {
                    todo!()
                };

                let var = self.lookup_name(&name);
                let ty = self.var_ty(var);

                Expr::new(ty, ExprData::Ident(var))
            }
            mist_syntax::ast::Expr::NullExpr(_) => Expr::new(
                Type::new(self.db, TypeData::Null),
                ExprData::Literal(Literal::Null),
            ),
            mist_syntax::ast::Expr::ResultExpr(_) => {
                let ty = if let Some(return_ty) = self.return_ty {
                    return_ty
                } else {
                    self.push_error(
                        expr.span(),
                        None,
                        None,
                        TypeCheckErrorKind::ResultWithNoReturn,
                    )
                };
                Expr::new(ty, ExprData::Result)
            }
            mist_syntax::ast::Expr::QuantifierExpr(it) => {
                let quantifier = match it.quantifier() {
                    Some(q) if q.forall_token().is_some() => Quantifier::Forall,
                    Some(q) if q.exists_token().is_some() => Quantifier::Exists,
                    None => todo!(),
                    _ => todo!(),
                };
                let params = check_param_list(self.db, self.program, it.param_list());

                self.push_scope();
                for param in &params.params {
                    self.declare_variable(&param.name, param.ty);
                }

                let expr = self.check(it.span(), it.expr());
                self.pop_scope();

                Expr::new(
                    Type::bool(self.db),
                    ExprData::Quantifier {
                        quantifier,
                        params,
                        expr,
                    },
                )
            }
        };

        self.trace.alloc(Some(expr), new)
    }
    fn pretty_ty(&self, ty: Type) -> String {
        ir::pretty::ty(self, self.db, ty)
    }
    fn expect_ty(&mut self, span: SourceSpan, expected: Type, actual: Type) -> Type {
        self.unify_inner(expected, actual).unwrap_or_else(|| {
            self.push_error(
                span,
                None,
                None,
                TypeCheckErrorKind::Mismatch {
                    expected: self.pretty_ty(expected),
                    actual: self.pretty_ty(actual),
                },
            )
        })
    }
    fn unify(&mut self, span: SourceSpan, t1: Type, t2: Type) -> Type {
        self.unify_inner(t1, t2).unwrap_or_else(|| {
            self.push_error(
                span,
                None,
                None,
                TypeCheckErrorKind::CantUnify(self.pretty_ty(t1), self.pretty_ty(t2)),
            )
        })
    }
    fn unify_inner(&mut self, t1: Type, t2: Type) -> Option<Type> {
        Some(match (t1.data(self.db), t2.data(self.db)) {
            (TypeData::Error, _) | (_, TypeData::Error) => t1,
            (TypeData::Void, TypeData::Void) => t1,
            (
                &TypeData::Ref {
                    is_mut: mut1,
                    inner: inner1,
                },
                &TypeData::Ref {
                    is_mut: mut2,
                    inner: inner2,
                },
            ) => Type::new(
                self.db,
                TypeData::Ref {
                    is_mut: mut1 && mut2,
                    inner: self.unify_inner(inner1, inner2)?,
                },
            ),
            (TypeData::Optional { inner: inner1 }, TypeData::Optional { inner: inner2 })
                if inner1 == inner2 =>
            {
                t1
            }
            (TypeData::Optional { inner }, TypeData::Struct(_)) if *inner == t2 => t1,
            (TypeData::Struct(_), TypeData::Optional { inner }) if *inner == t1 => t2,
            (TypeData::Primitive(p1), TypeData::Primitive(p2)) if p1 == p2 => t1,
            (TypeData::Struct(s1), TypeData::Struct(s2)) => {
                if s1 == s2 {
                    t1
                } else {
                    todo!()
                }
            }
            (TypeData::Null, TypeData::Null) => t1,
            (TypeData::Null, TypeData::Optional { .. }) => t2,
            (TypeData::Optional { .. }, TypeData::Null) => t1,
            _ => return None,
        })
    }
    fn push_error(
        &self,
        span: SourceSpan,
        label: Option<String>,
        help: Option<String>,
        kind: TypeCheckErrorKind,
    ) -> Type {
        let err = TypeCheckError {
            input: self.program.program(self.db).to_string(),
            span,
            label,
            help,
            kind,
        };
        TypeCheckErrors::push(self.db, err.clone());
        eprintln!("{:?}", miette::Error::new(err));
        Type::new(self.db, TypeData::Error)
    }
    fn expr_error(
        &mut self,
        span: SourceSpan,
        label: Option<String>,
        help: Option<String>,
        kind: TypeCheckErrorKind,
    ) -> ExprIdx {
        self.push_error(span, label, help, kind);

        self.trace
            .alloc(None, Expr::new(Type::error(self.db), ExprData::Missing))
    }
    pub fn check_boolean_exprs(
        &mut self,
        exprs: impl Iterator<Item = mist_syntax::ast::CommaExpr>,
    ) -> Vec<ExprIdx> {
        let bool_ty = Type::bool(self.db);
        exprs
            .map(|comma_expr| self.check(comma_expr.span(), comma_expr.expr()))
            .collect()
    }
    fn check_assertion(
        &mut self,
        kind: AssertionKind,
        exprs: impl Iterator<Item = mist_syntax::ast::CommaExpr>,
    ) -> Statement {
        Statement {
            data: StatementData::Assertion {
                kind,
                exprs: self.check_boolean_exprs(exprs),
            },
        }
    }
    fn find_type(&self, ty: mist_syntax::ast::Type) -> Type {
        crate::ir::find_type(self.db, self.program, ty)
    }
    pub fn check_block(&mut self, block: mist_syntax::ast::Block) -> Block {
        self.push_scope();
        let stmts = block
            .statements()
            .map(|stmt| match stmt {
                mist_syntax::ast::Stmt::LetStmt(it) => {
                    let name = it.name().unwrap();
                    let ty = if let Some(ty) = it.ty() {
                        Some(self.find_type(ty))
                    } else {
                        None
                    };
                    let initializer = self.check(it.span(), it.initializer());

                    let ty = if let Some(ty) = ty {
                        ty
                    } else {
                        self.trace.arena[initializer].ty
                    };

                    let variable = self.declare_variable(&name, ty);

                    Statement {
                        data: StatementData::Let {
                            variable,
                            initializer,
                        },
                    }
                }
                mist_syntax::ast::Stmt::Item(_) => todo!(),
                mist_syntax::ast::Stmt::ExprStmt(it) => {
                    Statement::new(StatementData::Expr(self.check(it.span(), it.expr())))
                }
                mist_syntax::ast::Stmt::AssertStmt(it) => {
                    self.check_assertion(AssertionKind::Assert, it.comma_exprs())
                }
                mist_syntax::ast::Stmt::AssumeStmt(it) => {
                    self.check_assertion(AssertionKind::Assume, it.comma_exprs())
                }
                mist_syntax::ast::Stmt::ReturnStmt(it) => {
                    if let Some(expr) = it.expr() {
                        let expr_span = expr.span();
                        let expr_idx = self.check(expr.span(), Some(expr));

                        let return_ty = self.return_ty.unwrap_or_else(|| Type::void(self.db));
                        self.expect_ty(expr_span, return_ty, self.expr_ty(expr_idx));

                        Statement::new(StatementData::Return(Some(expr_idx)))
                    } else {
                        Statement::new(StatementData::Return(None))
                    }
                }
                mist_syntax::ast::Stmt::WhileStmt(it) => Statement {
                    data: StatementData::While {
                        expr: self.check(it.span(), it.expr()),
                        invariants: it
                            .invariants()
                            .map(|inv| self.check_boolean_exprs(inv.comma_exprs()))
                            .collect(),
                        body: self.check_block(it.block().unwrap()),
                    },
                },
            })
            .collect();
        self.pop_scope();
        Block {
            stmts,
            return_ty: Type::new(self.db, TypeData::Void),
        }
    }
    pub fn declare_variable(&mut self, name: &mist_syntax::ast::Name, ty: Type) -> Idx<Variable> {
        let var = self.declarations.alloc(
            name.clone(),
            Variable::new(self.db, VariableId::new(self.db, name.to_string())),
        );
        self.scope.insert(name.to_string(), var);
        self.types.insert(var, ty);
        var
    }
    pub fn var_ty(&self, var: Idx<Variable>) -> Type {
        *self
            .types
            .get(var)
            .expect("Idx<Variable> was not in types map")
    }
    pub fn lookup_name(&mut self, name: &mist_syntax::ast::Name) -> Idx<Variable> {
        if let Some(var) = self.scope.get(&name.to_string()) {
            *var
        } else {
            let err_ty = self.push_error(
                name.span(),
                None,
                None,
                TypeCheckErrorKind::UndefinedVariable(name.to_string()),
            );
            self.declare_variable(name, err_ty)
        }
    }

    fn find_named_type(&self, name: mist_syntax::ast::Name) -> Type {
        crate::ir::find_named_type(self.db, self.program, name)
    }

    fn struct_fields(&self, s: crate::ir::Struct) -> Vec<StructField> {
        crate::ir::struct_fields(self.db, self.program, s)
    }
}
pub fn check_param_list(
    db: &dyn crate::Db,
    program: Program,
    param_list: Option<mist_syntax::ast::ParamList>,
) -> ParamList {
    ParamList {
        params: param_list
            .map(|pl| {
                pl.params()
                    .map(|p| Param {
                        name: if let Some(name) = p.name() {
                            name
                        } else {
                            todo!()
                        },
                        ty: if let Some(ty) = p.ty() {
                            crate::ir::find_type(db, program, ty)
                        } else {
                            Type::new(db, TypeData::Error)
                        },
                    })
                    .collect()
            })
            .unwrap_or_default(),
    }
}

impl ir::pretty::PrettyPrint for FunctionContext {
    fn resolve_var(&self, idx: la_arena::Idx<Variable>) -> String {
        self.declarations.map[idx].to_string()
    }

    fn resolve_expr(&self, idx: ExprIdx) -> &Expr {
        &self.trace.arena[idx]
    }
}

impl ir::pretty::PrettyPrint for TypeCheckExpr<'_> {
    fn resolve_var(&self, idx: la_arena::Idx<Variable>) -> String {
        self.declarations.map[idx].to_string()
    }

    fn resolve_expr(&self, idx: ExprIdx) -> &Expr {
        &self.trace.arena[idx]
    }
}

impl FunctionContext {
    pub fn pretty_expr(&self, db: &dyn crate::Db, expr: ExprIdx) -> String {
        ir::pretty::expr(self, db, expr)
    }
}

#[salsa::accumulator]
pub struct TypeCheckErrors(TypeCheckError);

#[derive(Debug, Diagnostic, Clone, Eq, PartialEq, Error)]
#[error("{kind}")]
pub struct TypeCheckError {
    #[source_code]
    pub input: String,
    #[label("{}", label.as_deref().unwrap_or("here"))]
    pub span: SourceSpan,
    pub label: Option<String>,
    #[help]
    pub help: Option<String>,
    pub kind: TypeCheckErrorKind,
}

#[derive(Debug, Diagnostic, Clone, Eq, PartialEq, Error)]
pub enum TypeCheckErrorKind {
    #[error("type `{0}` was not found")]
    UndefinedType(String),
    #[error("variable `{0}` was not found in this scope")]
    UndefinedVariable(String),
    #[error("missing initializer")]
    MissingInitializer,
    #[error("can't unify `{0}` with `{1}`")]
    CantUnify(String, String),
    #[error("missing left-hand-side of binary operation")]
    MissingLhs,
    #[error("missing right-hand-side of binary operation")]
    MissingRhs,
    #[error("missing expression")]
    MissingExpression,
    #[error("`result` used in function that does not have a return type")]
    ResultWithNoReturn,
    #[error("expected type `{expected}`, but found `{actual}`")]
    Mismatch { expected: String, actual: String },
    #[error("returned valued in function that did not return anything")]
    ReturnedValueWithNoReturnValue,
    #[error("the field `{field}` does not exist on struct `{strukt}`")]
    UnknownStructField { field: String, strukt: String },
}
