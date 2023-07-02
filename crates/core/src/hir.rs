pub mod def;
pub(crate) mod file_context;
mod item_context;
pub mod pretty;
pub mod typecheck;

use mist_syntax::ast::{HasName, Spanned};

use crate::{
    def::{Def, DefKind},
    file::SourceFile,
    hir::typecheck::{Typed, TypingMutExt},
    types::primitive::*,
};

pub use def::*;
pub use item_context::{source_map::ItemSourceMap, ItemContext, Named, SpanOrAstPtr};
use typecheck::TypeChecker;

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
    let span = tracing::span!(tracing::Level::DEBUG, "hir::item_lower", "{}", def.display(db));
    let _enter = span.enter();

    match def.kind(db) {
        DefKind::Struct(_) => {
            let checker = TypeChecker::init(db, def);
            Some(DefinitionHir::from_tc(checker))
        }
        DefKind::StructField(_) => None,
        DefKind::TypeInvariant(ty_inv) => {
            let mut checker = TypeChecker::init(db, def);
            let ty_inv_ast = ty_inv.ast_node(db);
            let for_ty_span = ty_inv_ast.ty().map_or(ty_inv_ast.span().set_len(0), |ty| ty.span());
            if let Some(ast_body) = ty_inv_ast.block_expr() {
                let body = checker.check_block(&ast_body, |f| f);
                let ret = checker.expect_ty(for_ty_span, ghost_bool(), body.return_ty);
                let ret_ty = checker.unsourced_ty(ret);
                checker.set_return_ty(ret_ty);
                checker.set_body_expr_from_block(body, ast_body);
            }
            Some(DefinitionHir::from_tc(checker))
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
                let ret_ty = checker.lower_type(&ret_ast);
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
                    let ret_ty = ret_ty.with_ghost(&mut checker, is_ghost);
                    checker.expect_ty(ret_ast.span(), ret_ty.ty(db), body.return_ty);
                } else {
                    checker.expect_ty(name_span, void(), body.return_ty);
                }
                checker.set_body_expr_from_block(body, ast_body);
            }
            Some(DefinitionHir::from_tc(checker))
        }
    }
}
