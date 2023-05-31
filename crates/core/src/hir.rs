pub mod def;
pub mod file;
mod item_context;
pub mod pretty;
pub mod typecheck;
pub mod types;

use itertools::Itertools;
use mist_syntax::ast::{self, HasName, Spanned};

use crate::{
    def::{Def, DefKind, Function, Struct, TypeInvariant},
    hir::{self, typecheck::Typed},
};

pub use def::*;
pub use item_context::{ItemContext, ItemSourceMap, SpanOrAstPtr};
use typecheck::{builtin::*, TypeChecker};
pub use types::TypeTable;

#[salsa::input]
pub struct SourceFile {
    #[return_ref]
    pub text: String,
}

#[salsa::tracked]
pub fn file_definitions(db: &dyn crate::Db, file: SourceFile) -> Vec<Def> {
    let ast_map = file.ast_map(db);
    file::parse_file(db, file)
        .tree()
        .items()
        .filter_map(|item| match item {
            ast::Item::Fn(node) => Some(DefKind::from(Function::new(
                db,
                ast_map.ast_id(file, &node),
            ))),
            ast::Item::Struct(node) => {
                Some(DefKind::from(Struct::new(db, ast_map.ast_id(file, &node))))
            }
            ast::Item::TypeInvariant(node) => Some(DefKind::from(TypeInvariant::new(
                db,
                ast_map.ast_id(file, &node),
            ))),
            ast::Item::Const(_) | ast::Item::Macro(_) => None,
        })
        .map(|kind| Def::new(db, kind))
        .collect()
}

#[salsa::tracked]
pub struct DefinitionHir {
    pub def: Def,
    #[return_ref]
    pub cx: ItemContext,
    #[return_ref]
    pub source_map: ItemSourceMap,
}

#[salsa::tracked]
pub(crate) fn lower_def(db: &dyn crate::Db, def: Def) -> Option<DefinitionHir> {
    let span = tracing::span!(
        tracing::Level::DEBUG,
        "hir::item_lower",
        "{}",
        def.display(db)
    );
    let _enter = span.enter();

    match def.kind(db) {
        DefKind::Struct(_) => {
            let mut checker = TypeChecker::init(db, def);

            if let Some(self_ty) = checker.cx.self_ty() {
                let related_invs = file_definitions(db, def.file(db))
                    .into_iter()
                    .filter_map(|def| {
                        if let hir::DefKind::TypeInvariant(inv) = def.kind(db) {
                            if checker.find_named_type(&inv.ast_node(db), inv.name(db)) == self_ty {
                                return Some(inv);
                            }
                        }
                        None
                    })
                    .collect_vec();

                for ty_inv in related_invs {
                    let ty_inv_ast = ty_inv.ast_node(db);
                    if let Some(ast_body) = ty_inv_ast.block_expr() {
                        let body = checker.check_block(&ast_body, |f| f);
                        let ret = ghost_bool();
                        let name_span = ty_inv_ast.name_ref().unwrap().span();
                        checker.expect_ty(name_span, ret, body.return_ty);
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
        DefKind::StructField(_) => None,
        DefKind::TypeInvariant(ty_inv) => {
            let mut checker = TypeChecker::init(db, def);
            let ty_inv_ast = ty_inv.ast_node(db);
            if let Some(ast_body) = ty_inv_ast.block_expr() {
                let body = checker.check_block(&ast_body, |f| f);
                let name_span = ty_inv_ast.name_ref().unwrap().span();
                let ret = checker.expect_ty(name_span, bool().ghost(), body.return_ty);
                let ret_ty = checker.unsourced_ty(ret);
                checker.set_return_ty(ret_ty);
                checker.set_body_expr_from_block(body, ast_body);
            }
            Some(checker.into())
        }
        DefKind::Function(function) => {
            let mut checker = TypeChecker::init(db, def);
            let fn_ast = function.ast_node(db);
            let body = fn_ast.body().map(|ast_body| {
                let ty = checker.check_block(&ast_body, |f| f);
                (ast_body, ty)
            });
            let is_ghost = function.attrs(db).is_ghost();
            let ret_ty = if let Some(ret_ast) = fn_ast.ret() {
                let ret_ty = checker.find_type_src(&ret_ast);
                checker.set_return_ty(ret_ty);
                Some((ret_ast, ret_ty))
            } else {
                None
            };
            if let Some((ast_body, body)) = body {
                let name_span = fn_ast
                    .name()
                    .map(|n| n.span())
                    .unwrap_or_else(|| fn_ast.fn_token().unwrap().span());
                if let Some((ret_ast, ret_ty)) = ret_ty {
                    let ret_ty = ret_ty.with_ghost(is_ghost).ts(&mut checker);
                    checker.expect_ty(ret_ast.span(), checker.cx[ret_ty].ty, body.return_ty);
                } else {
                    checker.expect_ty(name_span, void().with_ghost(is_ghost), body.return_ty);
                }
                checker.set_body_expr_from_block(body, ast_body);
            }
            Some(checker.into())
        }
    }
}
