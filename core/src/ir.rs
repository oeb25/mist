use bitflags::bitflags;
use derive_more::Display;
use derive_new::new;
use mist_syntax::ast::{operators::BinaryOp, Item, Spanned};

pub use crate::typecheck::FunctionContext;
use crate::{
    typecheck::{self, TypeCheckError, TypeCheckErrorKind, TypeCheckExpr},
    TypeCheckErrors,
};

#[salsa::input]
pub struct SourceProgram {
    #[return_ref]
    pub text: String,
}

#[salsa::tracked]
pub struct Program {
    #[return_ref]
    pub program: mist_syntax::ast::SourceFile,
    #[return_ref]
    pub errors: Vec<mist_syntax::ParseError>,
}

#[salsa::tracked]
pub fn parse_program(db: &dyn crate::Db, source: SourceProgram) -> Program {
    let (program, errors) = mist_syntax::parse(source.text(db));
    Program::new(db, program, errors)
}

#[salsa::tracked]
pub fn top_level_type_decls(db: &dyn crate::Db, program: Program) -> Vec<TypeDecl> {
    program
        .program(db)
        .items()
        .filter_map(|item| match item {
            Item::Struct(s) => {
                let name = s.name().unwrap().to_string();
                let data = TypeDeclData::Struct(Struct::new(db, s));
                Some(TypeDecl::new(db, name, data))
            }
            _ => None,
        })
        .collect()
}

#[salsa::tracked]
pub fn struct_name(db: &dyn crate::Db, s: Struct) -> mist_syntax::ast::Name {
    s.node(db).name().unwrap()
}

#[salsa::tracked]
pub fn struct_fields(db: &dyn crate::Db, program: Program, s: Struct) -> Vec<StructField> {
    s.node(db)
        .struct_fields()
        .map(|f| StructField {
            name: f.name().unwrap().to_string(),
            ty: if let Some(ty) = f.ty() {
                find_type(db, program, ty)
            } else {
                todo!()
            },
        })
        .collect()
}

#[salsa::tracked]
pub struct TypeDecl {
    #[return_ref]
    pub name: String,
    pub data: TypeDeclData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeDeclData {
    Struct(Struct),
}

#[salsa::tracked]
pub struct Function {
    #[return_ref]
    pub syntax: mist_syntax::ast::Fn,
    #[return_ref]
    pub name: mist_syntax::ast::Name,
    pub attrs: Attrs,
    #[return_ref]
    pub param_list: ParamList,
    pub ret: Option<Type>,
}

#[salsa::tracked]
pub fn functions(db: &dyn crate::Db, program: Program) -> Vec<Function> {
    program
        .program(db)
        .items()
        .filter_map(|item| match item {
            Item::Fn(f) => {
                let name = if let Some(name) = f.name() {
                    name
                } else {
                    todo!()
                };
                let attrs = f.attrs().fold(Attrs::NONE, |acc, a| match a {
                    a if a.ghost_token().is_some() => acc | Attrs::GHOST,
                    a if a.pure_token().is_some() => acc | Attrs::PURE,
                    _ => acc,
                });
                let param_list = typecheck::check_param_list(db, program, f.param_list());
                let ret_ty = f.ret().map(|ty| find_type(db, program, ty));

                Some(Function::new(db, f, name, attrs, param_list, ret_ty))
            }
            _ => None,
        })
        .collect()
}
fn function_checker(db: &dyn crate::Db, program: Program, function: Function) -> TypeCheckExpr {
    let mut checker = TypeCheckExpr::new(db, program, function.ret(db));

    for f in functions(db, program) {
        checker.declare_variable(
            f.name(db),
            Type::new(
                db,
                TypeData::Function {
                    params: f
                        .param_list(db)
                        .params
                        .iter()
                        .map(|param| param.ty)
                        .collect(),
                    return_ty: f.ret(db).unwrap_or_else(|| Type::new(db, TypeData::Void)),
                },
            ),
        );
    }

    for p in &function.param_list(db).params {
        checker.declare_variable(&p.name, p.ty);
    }
    checker
}
pub fn function_conditions(
    db: &dyn crate::Db,
    program: Program,
    function: Function,
) -> (FunctionContext, Vec<Condition>) {
    let mut checker = function_checker(db, program, function);
    let conditions = function
        .syntax(db)
        .conditions()
        .map(|c| match c {
            mist_syntax::ast::Condition::Requires(r) => {
                Condition::Requires(checker.check_boolean_exprs(r.comma_exprs()))
            }
            mist_syntax::ast::Condition::Ensures(r) => {
                Condition::Ensures(checker.check_boolean_exprs(r.comma_exprs()))
            }
        })
        .collect();
    (checker.into(), conditions)
}
#[salsa::tracked]
pub fn function_body(
    db: &dyn crate::Db,
    program: Program,
    function: Function,
) -> Option<(FunctionContext, Block)> {
    function.syntax(db).body().map(|body| {
        let mut checker = function_checker(db, program, function);
        let body = checker.check_block(body);
        if let Some(ret) = function.ret(db) {
            checker.expect_ty(
                function
                    .syntax(db)
                    .ret()
                    .map(|ret| ret.span())
                    .unwrap_or_else(|| function.name(db).span()),
                ret,
                body.return_ty,
            );
        } else {
            checker.expect_ty(function.name(db).span(), Type::void(db), body.return_ty);
        }
        (checker.into(), body)
    })
}

#[salsa::tracked]
pub fn structs(db: &dyn crate::Db, program: Program) -> Vec<Struct> {
    top_level_type_decls(db, program)
        .into_iter()
        .filter_map(|it| match it.data(db) {
            TypeDeclData::Struct(s) => Some(s),
        })
        .collect()
}

#[salsa::tracked]
pub fn find_named_type(db: &dyn crate::Db, program: Program, name: mist_syntax::ast::Name) -> Type {
    for item in top_level_type_decls(db, program) {
        if item.name(db) == &name.to_string() {
            match item.data(db) {
                TypeDeclData::Struct(it) => return Type::new(db, TypeData::Struct(it)),
            }
        }
    }

    let err = TypeCheckError {
        input: program.program(db).to_string(),
        span: name.span(),
        label: None,
        help: None,
        kind: TypeCheckErrorKind::UndefinedType(name.to_string()),
    };
    TypeCheckErrors::push(db, err);

    Type::new(db, TypeData::Error)
}
#[salsa::tracked]
pub fn find_type(db: &dyn crate::Db, program: Program, ty: mist_syntax::ast::Type) -> Type {
    match ty {
        mist_syntax::ast::Type::NamedType(name) => {
            find_named_type(db, program, name.name().unwrap())
            // let result = find_type_with_name(db, program, VariableId::new(db, name.to_string()));

            // if let Some(ty) = result {
            //     ty
            // } else {
            //     let range = name.ident_token().unwrap().text_range();
            //     let err = TypeCheckError {
            //         input: program.program(db).to_string(),
            //         span: SourceSpan::new_start_end(range.start().into(), range.end().into()),
            //         label: None,
            //         help: None,
            //         kind: TypeCheckErrorKind::UndefinedType(name.to_string()),
            //     };
            //     eprintln!("{:?}", miette::Error::new(err));

            //     Type::new(db, TypeData::Error)
            // }
        }
        mist_syntax::ast::Type::Primitive(it) => match () {
            _ if it.int_token().is_some() => Type::new(db, TypeData::Primitive(Primitive::Int)),
            _ if it.bool_token().is_some() => Type::new(db, TypeData::Primitive(Primitive::Bool)),
            _ => {
                todo!();
                Type::new(db, TypeData::Error)
            }
        },
        mist_syntax::ast::Type::Optional(it) => {
            if let Some(ty) = it.ty() {
                let inner = find_type(db, program, ty);
                Type::new(db, TypeData::Optional { inner })
            } else {
                todo!()
            }
        }
        mist_syntax::ast::Type::RefType(r) => {
            let is_mut = r.mut_token().is_some();

            if let Some(ty) = r.ty() {
                let inner = find_type(db, program, ty);
                Type::new(db, TypeData::Ref { is_mut, inner })
            } else {
                let err = TypeCheckError {
                    input: program.program(db).to_string(),
                    span: r.span(),
                    label: None,
                    help: None,
                    kind: TypeCheckErrorKind::UndefinedType("what is this".to_string()),
                };
                eprintln!("{:?}", miette::Error::new(err));
                todo!()
            }
        }
    }
}

// #[salsa::tracked]
// pub fn find_type_with_name(db: &dyn crate::Db, program: Program, name: VariableId) -> Option<Type> {
//     let decls = top_level_type_decls(db, program);

//     for decl in decls {
//         if decl.name(db) == name.text(db) {
//             return Some(decl.ty(db));
//         }
//     }

//     None
// }

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct Attrs: u32 {
        const NONE = 0b00;
        const GHOST = 0b01;
        const PURE = 0b10;
    }
}

#[salsa::interned]
pub struct VariableId {
    #[return_ref]
    pub text: String,
}

#[salsa::tracked]
pub struct Variable {
    #[id]
    pub name: VariableId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ParamList {
    pub params: Vec<Param>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Param {
    pub name: mist_syntax::ast::Name,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Condition {
    Requires(Vec<ExprIdx>),
    Ensures(Vec<ExprIdx>),
}

pub type ExprIdx = la_arena::Idx<Expr>;
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expr {
    pub ty: Type,
    pub data: ExprData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExprData {
    Literal(Literal),
    Ident(la_arena::Idx<Variable>),
    Field {
        expr: ExprIdx,
        field: String,
    },
    Struct {
        strukt: Struct,
        fields: Vec<StructExprField>,
    },
    Missing,
    If(IfExpr),
    Call {
        expr: ExprIdx,
        args: Vec<ExprIdx>,
    },
    Bin {
        lhs: ExprIdx,
        op: BinaryOp,
        rhs: ExprIdx,
    },
    Ref {
        is_mut: bool,
        expr: ExprIdx,
    },
    Quantifier {
        quantifier: Quantifier,
        params: ParamList,
        expr: ExprIdx,
    },
    Result,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    Null,
    Int(i64),
    Bool(bool),
}
#[derive(Debug, Display, Clone, PartialEq, Eq, Hash)]
pub enum Quantifier {
    #[display(fmt = "forall")]
    Forall,
    #[display(fmt = "exists")]
    Exists,
}
#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructExprField {
    pub name: String,
    pub value: ExprIdx,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct IfExpr {
    pub return_ty: Type,
    pub condition: ExprIdx,
    pub then_branch: Block,
    pub else_branch: Option<Box<Else>>,
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Else {
    If(IfExpr),
    Block(Block),
}
impl Else {
    pub fn return_ty(&self, db: &dyn crate::Db) -> Type {
        match self {
            Else::If(it) => it.return_ty,
            Else::Block(it) => it.return_ty,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    pub stmts: Vec<Statement>,
    pub tail_expr: Option<ExprIdx>,
    pub return_ty: Type,
}

#[derive(new, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Statement {
    pub data: StatementData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StatementData {
    Return(Option<ExprIdx>),
    Expr(ExprIdx),
    Let {
        variable: la_arena::Idx<Variable>,
        initializer: ExprIdx,
    },
    While {
        expr: ExprIdx,
        invariants: Vec<Vec<ExprIdx>>,
        body: Block,
    },
    Assertion {
        kind: AssertionKind,
        exprs: Vec<ExprIdx>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AssertionKind {
    Assert,
    Assume,
    Inhale,
    Exhale,
}

#[salsa::interned]
pub struct Type {
    #[return_ref]
    pub data: TypeData,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeData {
    Error,
    Void,
    Ref { is_mut: bool, inner: Type },
    Optional { inner: Type },
    Primitive(Primitive),
    Struct(Struct),
    Null,
    Function { params: Vec<Type>, return_ty: Type },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Primitive {
    Int,
    Bool,
}

#[salsa::tracked]
pub struct Struct {
    #[return_ref]
    node: mist_syntax::ast::Struct,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StructField {
    pub name: String,
    pub ty: Type,
}

pub mod pretty {
    use super::*;
    use itertools::Itertools;

    pub trait PrettyPrint {
        fn resolve_var(&self, idx: la_arena::Idx<Variable>) -> String;
        fn resolve_expr(&self, idx: ExprIdx) -> &Expr;
    }

    use expr as pp_expr;
    use params as pp_params;
    use ty as pp_ty;

    pub fn params(pp: &impl PrettyPrint, db: &dyn crate::Db, params: &ParamList) -> String {
        format!(
            "({})",
            params
                .params
                .iter()
                .map(|param| format!("{}: {}", param.name, pp_ty(pp, db, param.ty)))
                .format(", ")
        )
    }
    pub fn ty(_pp: &impl PrettyPrint, db: &dyn crate::Db, ty: Type) -> String {
        match ty.data(db) {
            TypeData::Error => "Error".to_string(),
            TypeData::Void => "void".to_string(),
            &TypeData::Ref { is_mut, inner } => {
                format!(
                    "&{}{}",
                    if is_mut { "mut " } else { "" },
                    pp_ty(_pp, db, inner)
                )
            }
            &TypeData::Optional { inner } => format!("{}?", pp_ty(_pp, db, inner)),
            TypeData::Primitive(t) => format!("{t:?}").to_lowercase(),
            TypeData::Struct(s) => struct_name(db, *s).to_string(),
            TypeData::Null => "null".to_string(),
            TypeData::Function { params, return_ty } => format!(
                "fn({}) -> {}",
                params.iter().map(|t| pp_ty(_pp, db, *t)).format(", "),
                pp_ty(_pp, db, *return_ty)
            ),
        }
    }
    pub fn expr(pp: &impl PrettyPrint, db: &dyn crate::Db, expr: ExprIdx) -> String {
        match &pp.resolve_expr(expr).data {
            ExprData::Literal(l) => match l {
                Literal::Null => "null".to_string(),
                Literal::Int(i) => i.to_string(),
                Literal::Bool(b) => b.to_string(),
            },
            ExprData::Ident(i) => pp.resolve_var(*i),
            ExprData::Field { expr, field } => format!("{}.{field}", pp_expr(pp, db, *expr)),
            ExprData::Struct { strukt, fields } => format!(
                "{} {{ {} }}",
                struct_name(db, *strukt),
                fields
                    .iter()
                    .map(|f| format!("{}: {}", f.name, pp_expr(pp, db, f.value)))
                    .format(", ")
            ),
            ExprData::Missing => "<missing>".to_string(),
            ExprData::If(it) => format!("if {}", pp_expr(pp, db, it.condition)),
            ExprData::Call { expr, args } => format!(
                "{}({})",
                pp_expr(pp, db, *expr),
                args.iter().map(|arg| pp_expr(pp, db, *arg)).format(", ")
            ),
            ExprData::Bin { lhs, op, rhs } => {
                format!("({} {op} {})", pp_expr(pp, db, *lhs), pp_expr(pp, db, *rhs))
            }
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
                pp_params(pp, db, params),
                pp_expr(pp, db, *expr)
            ),
            ExprData::Result => "result".to_string(),
        }
    }
}
