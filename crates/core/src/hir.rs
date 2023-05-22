pub mod def;
mod item_context;
pub mod typecheck;
pub mod types;

use itertools::Itertools;
use mist_syntax::{
    ast::{self, HasAttrs, HasName, Spanned},
    ptr::AstPtr,
    Parse,
};

use crate::{
    hir::{self, typecheck::Typed},
    TypeCheckErrors,
};

pub use def::*;
pub use item_context::{ItemContext, ItemSourceMap, SpanOrAstPtr};
use typecheck::{builtin::*, TypeCheckError, TypeCheckErrorKind, TypeChecker};
pub use types::TypeTable;

pub mod pretty;

#[salsa::input]
pub struct SourceProgram {
    #[return_ref]
    pub text: String,
}

#[salsa::tracked]
pub struct Program {
    #[return_ref]
    pub parse: Parse<ast::SourceFile>,
    #[return_ref]
    pub items: Vec<ItemId>,
}

#[salsa::tracked]
pub fn parse_program(db: &dyn crate::Db, source: SourceProgram) -> Program {
    let parse = mist_syntax::parse(source.text(db));
    let items = parse
        .tree()
        .items()
        .map(|item| match item {
            ast::Item::Const(node) => ItemId::new(db, AstPtr::new(&node).into()),
            ast::Item::Fn(node) => ItemId::new(db, AstPtr::new(&node).into()),
            ast::Item::Struct(node) => ItemId::new(db, AstPtr::new(&node).into()),
            ast::Item::TypeInvariant(node) => ItemId::new(db, AstPtr::new(&node).into()),
            ast::Item::Macro(node) => ItemId::new(db, AstPtr::new(&node).into()),
        })
        .collect();
    Program::new(db, parse, items)
}

#[salsa::tracked]
pub fn intern_item(db: &dyn crate::Db, program: Program, item_id: ItemId) -> Option<Item> {
    let root = program.parse(db).tree();
    item(db, &root, item_id)
}

pub fn item(db: &dyn crate::Db, root: &ast::SourceFile, item_id: ItemId) -> Option<Item> {
    Some(match item_id.data(db) {
        ItemData::Const { .. } => return None,
        ItemData::Fn { ast } => {
            let f = ast.to_node(root.syntax());
            let name = f.name().unwrap();
            let attrs = f.attr_flags();

            if !f.is_ghost() && f.body().is_none() {
                let err = TypeCheckError {
                    input: root.to_string(),
                    span: f
                        .semicolon_token()
                        .map(|t| t.span())
                        .unwrap_or_else(|| name.span()),
                    label: None,
                    help: None,
                    kind: TypeCheckErrorKind::NonGhostFunctionWithoutBody,
                };
                TypeCheckErrors::push(db, err);
            }

            Function::new(db, ast, name.into(), attrs).into()
        }
        ItemData::Struct { ast } => {
            let s = ast.to_node(root.syntax());
            let name = Ident::from(s.name().unwrap());
            let fields = s
                .struct_fields()
                .map(|f| {
                    let is_ghost = f.is_ghost();
                    let name = f.name().unwrap();
                    StructFieldInner {
                        name: name.into(),
                        is_ghost,
                        ty: f.ty().as_ref().map(AstPtr::new),
                    }
                })
                .collect();
            let data = TypeDeclData::Struct(Struct::new(db, ast, name.clone(), fields));
            TypeDecl::new(db, name, data).into()
        }
        ItemData::TypeInvariant { ast } => {
            let i = ast.to_node(root.syntax());
            let name = Ident::from(i.name_ref().unwrap());
            TypeInvariant::new(db, ast, name).into()
        }
        ItemData::Macro { .. } => return None,
    })
}

#[salsa::tracked]
pub fn item_lower(
    db: &dyn crate::Db,
    program: Program,
    item_id: ItemId,
    item: Item,
) -> Option<(ItemContext, ItemSourceMap)> {
    let span = tracing::span!(
        tracing::Level::DEBUG,
        "hir::item_lower",
        "{}",
        item.name(db)
    );
    let _enter = span.enter();

    let root = program.parse(db).tree();

    match item {
        Item::Type(ty_decl) => match &ty_decl.data(db) {
            TypeDeclData::Struct(_) => {
                let mut checker = TypeChecker::init(db, program, &root, item_id);

                if let Some(self_ty) = checker.cx.self_ty() {
                    let related_invs = program
                        .items(db)
                        .iter()
                        .filter_map(|&item_id| {
                            if let Some(hir::Item::TypeInvariant(inv)) =
                                hir::item(db, &root, item_id)
                            {
                                if checker.find_named_type(inv.name(db)) == self_ty {
                                    return Some(inv);
                                }
                            }
                            None
                        })
                        .collect_vec();

                    for ty_inv in related_invs {
                        if let Some(ast_body) = ty_inv.body(db, &root) {
                            let body = checker.check_block(&ast_body, |f| f);
                            let ret = ghost_bool();
                            checker.expect_ty(ty_inv.name(db).span(), ret, body.return_ty);
                            let body_expr = checker.alloc_expr(
                                ExprData::Block(body).typed(ret),
                                &ast::Expr::from(ast_body),
                            );
                            checker.cx.self_invariants.push(body_expr);
                        }
                    }
                }

                Some(checker.into())
            }
        },
        Item::TypeInvariant(ty_inv) => {
            let mut checker = TypeChecker::init(db, program, &root, item_id);
            if let Some(ast_body) = ty_inv.body(db, &root) {
                let body = checker.check_block(&ast_body, |f| f);
                let ret = bool().ghost();
                checker.expect_ty(ty_inv.name(db).span(), ret, body.return_ty);
                let ret_ty = checker.unsourced_ty(ret);
                checker.set_return_ty(ret_ty);
                checker.set_body_expr_from_block(body, ast_body);
            }
            Some(checker.into())
        }
        Item::Function(function) => {
            let mut checker = TypeChecker::init(db, program, &root, item_id);
            let ast_body = function.body(db, &root);
            let body = ast_body
                .as_ref()
                .map(|ast_body| checker.check_block(ast_body, |f| f));
            let is_ghost = function.attrs(db).is_ghost();
            if let Some(body) = body {
                if let Some(ret) = function.ret(db, &root) {
                    let ret = checker
                        .find_type_src(&ret)
                        .with_ghost(is_ghost)
                        .ts(&mut checker);
                    checker.expect_ty(
                        function
                            .ret(db, &root)
                            .map(|ret| ret.span())
                            .unwrap_or_else(|| function.name(db).span()),
                        checker.cx[ret].ty,
                        body.return_ty,
                    );
                } else {
                    checker.expect_ty(
                        function.name(db).span(),
                        void().with_ghost(is_ghost),
                        body.return_ty,
                    );
                }
                checker.set_body_expr_from_block(body, ast_body.unwrap());
            }
            if let Some(ret) = function.ret(db, &root) {
                let ret_ty = checker.find_type_src(&ret);
                checker.set_return_ty(ret_ty);
            }
            Some(checker.into())
        }
    }
}
