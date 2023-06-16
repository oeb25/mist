mod tokens;

use std::{ops::ControlFlow, sync::Arc};

use derive_new::new;
use itertools::Itertools;
use mist_core::{
    hir::{self, file, ExprIdx, SourceFile, TypeRefKind, TypeSrc, VariableIdx},
    mir::{self, pass::Pass},
    salsa,
    types::TDK,
    util::Position,
    visit::{PostOrderWalk, VisitContext, Visitor, Walker},
};
use mist_syntax::{
    ast::{self, Spanned},
    SourceSpan,
};
pub use tokens::{TokenModifier, TokenType};
use tower_lsp::lsp_types::{self, SemanticToken};

#[allow(unused)]
use TokenModifier as TM;
use TokenType as TT;

#[salsa::tracked]
pub fn highlighting(db: &dyn crate::Db, file: SourceFile) -> Arc<HighlightResult> {
    let root = file::parse_file(db, file).tree();
    let mut hf = Highlighter::new(db, file.text(db), &root);
    let _ = PostOrderWalk::walk_program(db, file, &mut hf);
    Arc::new(hf.finish())
}

#[salsa::tracked]
pub fn semantic_tokens(db: &dyn crate::Db, source: SourceFile) -> Arc<Vec<SemanticToken>> {
    let result = highlighting(db, source);
    Arc::clone(&result.tokens)
}
const ANNOTATE_BAD_FOLDINGS: bool = false;
#[salsa::tracked]
pub fn inlay_hints(db: &dyn crate::Db, source: SourceFile) -> Arc<Vec<InlayHint>> {
    let mut inlay_hints = highlighting(db, source).inlay_hints.clone();
    let result = Arc::make_mut(&mut inlay_hints);

    if ANNOTATE_BAD_FOLDINGS {
        source
            .definitions(db)
            .into_iter()
            .filter_map(|def| {
                let mir = def.mir(db)?;
                let hir = def.hir(db)?;
                let cx = hir.cx(db);
                let source_map = hir.source_map(db);
                let mir_source_map = mir.source_map(db);
                let mut body = mir.body(db).clone();
                mir::pass::FullDefaultPass::run(db, &mut body);

                let cfg = mir::analysis::cfg::Cfg::compute(&body);
                for entry in body.entry_blocks() {
                    cfg.visit_reverse_post_order(entry, |bid| {
                        let mut stacked_up = vec![];
                        for inst in body[bid].locations().filter_map(|loc| loc.as_instruction()) {
                            if let mir::Instruction::Folding(f) = &body[inst] {
                                stacked_up.push(f)
                            }

                            let Some(expr) = mir_source_map.trace_expr(inst) else { continue };

                            for f in stacked_up.drain(..) {
                                let p = mir::serialize::serialize_place(
                                    mir::serialize::Color::No,
                                    Some(db),
                                    Some(cx),
                                    &body,
                                    f.place(),
                                );
                                result.push(InlayHint {
                                    position: Position::from_byte_offset(
                                        source.text(db),
                                        source_map[expr].span().offset(),
                                    ),
                                    label: match f {
                                        mir::Folding::Fold { .. } => format!("fold {p}"),
                                        mir::Folding::Unfold { .. } => format!("unfold {p}"),
                                    },
                                    kind: None,
                                    padding_left: None,
                                    padding_right: Some(true),
                                });
                            }
                        }
                    })
                }
                Some(())
            })
            .for_each(drop);
    }
    inlay_hints
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InlayHint {
    pub position: Position,
    pub label: String,
    pub kind: Option<lsp_types::InlayHintKind>,
    pub padding_left: Option<bool>,
    pub padding_right: Option<bool>,
}

impl From<InlayHint> for lsp_types::InlayHint {
    fn from(hint: InlayHint) -> Self {
        Self {
            position: lsp_types::Position {
                line: hint.position.line,
                character: hint.position.character,
            },
            label: lsp_types::InlayHintLabel::String(hint.label),
            kind: hint.kind,
            text_edits: None,
            tooltip: None,
            padding_left: hint.padding_left,
            padding_right: hint.padding_right,
            data: None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HighlightResult {
    tokens: Arc<Vec<SemanticToken>>,
    inlay_hints: Arc<Vec<InlayHint>>,
}

#[derive(new)]
struct Highlighter<'src> {
    db: &'src dyn crate::Db,
    src: &'src str,
    root: &'src ast::SourceFile,
    #[new(default)]
    tokens: Vec<SemanticToken>,
    #[new(default)]
    inlay_hints: Vec<InlayHint>,
}

impl<'src> Highlighter<'src> {
    pub fn push_opt(
        &mut self,
        span: Option<SourceSpan>,
        token_type: TokenType,
        token_modifiers: Option<TokenModifier>,
    ) -> &mut Self {
        if let Some(span) = span {
            self.push(span, token_type, token_modifiers)
        } else {
            self
        }
    }
    pub fn push(
        &mut self,
        span: impl Spanned,
        token_type: TokenType,
        _token_modifiers: Option<TokenModifier>,
    ) -> &mut Self {
        let span = span.span();
        let start = Position::from_byte_offset(self.src, span.offset());

        let token = SemanticToken {
            delta_line: start.line,
            delta_start: start.character,
            length: span.len() as _,
            token_type: token_type.into(),
            token_modifiers_bitset: 0,
        };

        if let Some(pos) = self
            .tokens
            .iter()
            .rposition(|t| (t.delta_line, t.delta_start) < (start.line, start.character))
        {
            self.tokens.insert(pos + 1, token);
        } else {
            self.tokens.insert(0, token);
        }

        self
    }
    pub fn finish(self) -> HighlightResult {
        let tokens = self
            .tokens
            .first()
            .cloned()
            .into_iter()
            .chain(self.tokens.iter().tuple_windows().map(|(a, b)| {
                let on_same_line = a.delta_line == b.delta_line;
                SemanticToken {
                    delta_line: b.delta_line - a.delta_line,
                    delta_start: if on_same_line {
                        b.delta_start - a.delta_start
                    } else {
                        b.delta_start
                    },
                    length: b.length,
                    token_type: b.token_type,
                    token_modifiers_bitset: b.token_modifiers_bitset,
                }
            }))
            .collect();

        HighlightResult { tokens: Arc::new(tokens), inlay_hints: Arc::new(self.inlay_hints) }
    }
}

impl<'src> Visitor for Highlighter<'src> {
    type Item = ();
    fn visit_var(
        &mut self,
        vcx: &VisitContext,
        var: VariableIdx,
        span: SourceSpan,
    ) -> ControlFlow<()> {
        use mist_core::VariableDeclarationKind::*;

        let tt = match vcx.cx.decl(var).kind() {
            Let => TT::Variable,
            Parameter => TT::Parameter,
            Function => TT::Function,
            Undefined => return ControlFlow::Continue(()),
        };
        self.push(span, tt, None);
        ControlFlow::Continue(())
    }
    fn visit_self(
        &mut self,
        _vcx: &VisitContext,
        src: &hir::SpanOrAstPtr<mist_syntax::ast::Expr>,
    ) -> ControlFlow<Self::Item> {
        self.push(src, TT::Keyword, None);
        ControlFlow::Continue(())
    }

    fn visit_param(
        &mut self,
        vcx: &VisitContext,
        param: &hir::Param<VariableIdx, TypeSrc>,
    ) -> ControlFlow<()> {
        self.push(vcx.cx.var_span(param.name), TT::Parameter, None);

        if param.ty.type_ref(self.db).is_none() {
            let span = vcx.cx.var_span(param.name);
            let ty = vcx.cx.var_ty(self.db, param.name);
            self.inlay_hints.push(InlayHint {
                position: Position::from_byte_offset(self.src, span.end()),
                label: format!(": {}", vcx.cx.pretty_ty(self.db, ty.id())),
                kind: None,
                padding_left: None,
                padding_right: None,
            });
        }

        ControlFlow::Continue(())
    }

    fn visit_expr(&mut self, vcx: &VisitContext, expr: ExprIdx) -> ControlFlow<()> {
        let src = vcx.source_map.expr_src(&vcx.cx, expr);
        let e = vcx.cx.original_expr(expr);
        match &e.data {
            hir::ExprData::Literal(_) => {
                let tt = match vcx.cx.expr_ty(expr).kind() {
                    TDK::Function { .. } => TT::Function,
                    TDK::Primitive(_) => TT::Number,
                    TDK::Null => TT::Number,
                    _ => return ControlFlow::Continue(()),
                };

                self.push(&src, tt, None);
            }
            hir::ExprData::Result => {
                self.push(&src, TT::Keyword, None);
            }
            hir::ExprData::Struct { .. } => {
                let ast = src.into_ptr().map(|n| n.to_node(self.root.syntax()));
                if let Some(ast::Expr::StructExpr(it)) = ast {
                    if let Some(t) = it.name_ref() {
                        self.push(t.span(), TT::Type, None);
                    }
                }
            }
            hir::ExprData::If(it) => {
                if it.is_ghost {
                    self.inlay_hints.push(InlayHint {
                        position: Position::from_byte_offset(self.src, src.span().offset()),
                        label: "ghost".to_string(),
                        kind: None,
                        padding_left: None,
                        padding_right: Some(true),
                    });
                }
            }
            _ => {}
        }

        ControlFlow::Continue(())
    }

    fn visit_ty(&mut self, vcx: &VisitContext, ts: hir::TypeSrc) -> ControlFlow<()> {
        match ts.type_ref(self.db) {
            Some(TypeRefKind::Primitive(_)) => {
                self.push_opt(Some(vcx.source_map[ts].span()), TT::Type, Some(TM::DefaultLibrary));
            }
            Some(TypeRefKind::Struct(_)) => {
                self.push_opt(Some(vcx.source_map[ts].span()), TT::Type, None);
            }
            _ => {}
        }

        ControlFlow::Continue(())
    }

    fn visit_stmt(&mut self, vcx: &VisitContext, stmt: hir::StatementId) -> ControlFlow<()> {
        if let hir::StatementData::Let(let_stmt) = &vcx.cx[stmt].data {
            let explicit_ty = vcx.source_map.stmt_ast(stmt).and_then(|ast| {
                let_stmt.explicit_ty(&ast.cast()?.to_node(self.root.syntax()), &vcx.source_map)
            });

            if explicit_ty.is_none() {
                let span = vcx.cx.var_span(let_stmt.variable);
                let ty = vcx.cx.var_ty(self.db, let_stmt.variable);
                self.inlay_hints.push(InlayHint {
                    position: Position::from_byte_offset(self.src, span.end()),
                    label: format!(": {}", vcx.cx.pretty_ty(self.db, ty.id())),
                    kind: None,
                    padding_left: None,
                    padding_right: None,
                });
            }
        }

        ControlFlow::Continue(())
    }
}
