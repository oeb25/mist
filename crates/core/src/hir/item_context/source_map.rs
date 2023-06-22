use std::collections::HashMap;

use mist_syntax::{
    ast::{self, Spanned},
    ptr::AstPtr,
    SourceSpan,
};
use tracing::info;

use crate::{
    hir::{ExprIdx, StatementId, TypeSrc},
    util::IdxMap,
};

use super::{ItemContext, Named, SpanOrAstPtr};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ItemSourceMap {
    name_map: HashMap<AstPtr<ast::NameOrNameRef>, Named>,
    name_map_back: HashMap<Named, Vec<AstPtr<ast::NameOrNameRef>>>,
    stmt_map: HashMap<AstPtr<ast::Stmt>, StatementId>,
    stmt_map_back: IdxMap<StatementId, AstPtr<ast::Stmt>>,
    expr_map: HashMap<SpanOrAstPtr<ast::Expr>, ExprIdx>,
    expr_map_back: IdxMap<ExprIdx, SpanOrAstPtr<ast::Expr>>,
    ty_src_map: HashMap<TypeSrc, SpanOrAstPtr<ast::Type>>,
    ty_src_map_back: HashMap<SpanOrAstPtr<ast::Type>, TypeSrc>,
}

#[derive(Debug, Clone, thiserror::Error)]
pub enum ItemSourceMapError {
    #[error("entry '{key}' already had a mapping (value: '{value}', type: '{ty}')")]
    AlreadyPresent { ty: &'static str, key: String, value: String },
}

impl ItemSourceMap {
    pub fn register_name(
        &mut self,
        name: AstPtr<ast::NameOrNameRef>,
        named: Named,
    ) -> Result<(), ItemSourceMapError> {
        info!(?named, "registering named");

        let old = self.name_map.insert(name.clone(), named.clone());
        self.name_map_back.entry(named).or_default().push(name.clone());
        if let Some(old) = old {
            Err(ItemSourceMapError::AlreadyPresent {
                ty: "AstPtr<ast::NameOrNameRef>",
                key: format!("{name:?}"),
                value: format!("{old:?}"),
            })
        } else {
            Ok(())
        }
    }
    pub fn register_stmt(
        &mut self,
        ast: AstPtr<ast::Stmt>,
        stmt: StatementId,
    ) -> Result<(), ItemSourceMapError> {
        let old = self.stmt_map.insert(ast.clone(), stmt);
        let old = old.and_then(|old| (old != stmt).then_some(old));
        self.stmt_map_back.insert(stmt, ast);
        if let Some(old) = old {
            Err(ItemSourceMapError::AlreadyPresent {
                ty: "Stmt",
                key: format!("{stmt:?}"),
                value: format!("{old:?}"),
            })
        } else {
            Ok(())
        }
    }
    pub fn register_expr(
        &mut self,
        ast: SpanOrAstPtr<ast::Expr>,
        expr: ExprIdx,
    ) -> Result<(), ItemSourceMapError> {
        let old = self.expr_map.insert(ast.clone(), expr);
        let old = old.and_then(|old| (old != expr).then_some(old));
        self.expr_map_back.insert(expr, ast);
        if let Some(old) = old {
            Err(ItemSourceMapError::AlreadyPresent {
                ty: "Expr",
                key: format!("{expr:?}"),
                value: format!("{old:?}"),
            })
        } else {
            Ok(())
        }
    }
    pub fn register_ty_src(
        &mut self,
        ty_src: TypeSrc,
        ast: SpanOrAstPtr<ast::Type>,
    ) -> Result<(), ItemSourceMapError> {
        let old = self.ty_src_map.insert(ty_src, ast.clone());
        let old = old.and_then(|old| (old != ast).then_some(old));
        self.ty_src_map_back.insert(ast, ty_src);
        if let Some(old) = old {
            Err(ItemSourceMapError::AlreadyPresent {
                ty: "TypeSrc",
                key: format!("{ty_src:?}"),
                value: format!("{old:?}"),
            })
        } else {
            Ok(())
        }
    }
}

impl ItemSourceMap {
    pub fn expr_src(&self, cx: &ItemContext, expr: ExprIdx) -> SpanOrAstPtr<ast::Expr> {
        if let Some(&desugared) = cx.desugared_back.get(expr) {
            self.expr_map_back[desugared].clone()
        } else {
            self.expr_map_back[expr].clone()
        }
    }
    pub fn expr_span(&self, cx: &ItemContext, expr: ExprIdx) -> SourceSpan {
        if let Some(&desugared) = cx.desugared_back.get(expr) {
            self.expr_map_back[desugared].span()
        } else {
            self.expr_map_back[expr].span()
        }
    }
    pub fn name_var(&self, name: &AstPtr<ast::NameOrNameRef>) -> Option<Named> {
        self.name_map.get(name).cloned()
    }
    pub fn named_references<'a>(
        &'a self,
        named: &Named,
    ) -> impl Iterator<Item = &'a AstPtr<ast::NameOrNameRef>> {
        self.name_map_back.get(named).into_iter().flatten()
    }
    pub fn names(&self) -> impl Iterator<Item = (&AstPtr<ast::NameOrNameRef>, &Named)> {
        self.name_map.iter()
    }
    pub fn stmt_ast(&self, stmt: StatementId) -> Option<AstPtr<ast::Stmt>> {
        self.stmt_map_back.get(stmt).cloned()
    }
    pub fn ty_src(&self, src: TypeSrc) -> Option<SpanOrAstPtr<ast::Type>> {
        self.ty_src_map.get(&src).cloned()
    }
    pub fn ty_ast(&self, ast: SpanOrAstPtr<ast::Type>) -> Option<TypeSrc> {
        self.ty_src_map_back.get(&ast).copied()
    }
}

impl std::ops::Index<ExprIdx> for ItemSourceMap {
    type Output = SpanOrAstPtr<ast::Expr>;

    fn index(&self, index: ExprIdx) -> &Self::Output {
        &self.expr_map_back[index]
    }
}
impl std::ops::Index<TypeSrc> for ItemSourceMap {
    type Output = SpanOrAstPtr<ast::Type>;

    fn index(&self, index: TypeSrc) -> &Self::Output {
        &self.ty_src_map[&index]
    }
}
