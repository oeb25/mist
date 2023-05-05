mod tokens;

use std::{ops::ControlFlow, sync::Arc};

use derive_new::new;
use itertools::Itertools;
use mist_core::{
    hir::{self, ExprIdx, SourceProgram, VariableIdx, VariableRef},
    salsa,
    util::Position,
    visit::{PostOrderWalk, VisitContext, Visitor, Walker},
};
use mist_syntax::{ast::Spanned, SourceSpan};
pub use tokens::{TokenModifier, TokenType};
use tower_lsp::lsp_types::{self, SemanticToken};

#[allow(unused)]
use TokenModifier as TM;
use TokenType as TT;

#[salsa::tracked]
pub fn highlighting(db: &dyn crate::Db, source: SourceProgram) -> Arc<HighlightResult> {
    let program = hir::parse_program(db, source);

    let mut hf = Highlighter::new(db, source.text(db));
    PostOrderWalk::walk_program(db, program, &mut hf);
    Arc::new(hf.finish())
}

#[salsa::tracked]
pub fn semantic_tokens(db: &dyn crate::Db, source: SourceProgram) -> Arc<Vec<SemanticToken>> {
    let result = highlighting(db, source);
    Arc::clone(&result.tokens)
}
#[salsa::tracked]
pub fn inlay_hints(db: &dyn crate::Db, source: SourceProgram) -> Arc<Vec<InlayHint>> {
    let result = highlighting(db, source);
    Arc::clone(&result.inlay_hints)
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

        HighlightResult {
            tokens: Arc::new(tokens),
            inlay_hints: Arc::new(self.inlay_hints),
        }
    }
}

impl<'src> Visitor for Highlighter<'src> {
    type Item = ();
    fn visit_var(&mut self, vcx: &VisitContext, var: VariableRef) -> ControlFlow<()> {
        use mist_core::VariableDeclarationKind::*;

        let tt = match vcx.cx.decl(var).kind() {
            Let => TT::Variable,
            Parameter => TT::Parameter,
            Function => TT::Function,
            Undefined => return ControlFlow::Continue(()),
        };
        self.push(var, tt, None);
        ControlFlow::Continue(())
    }

    fn visit_param(
        &mut self,
        vcx: &VisitContext,
        param: &hir::Param<VariableIdx>,
    ) -> ControlFlow<()> {
        self.push(vcx.cx.var_span(param.name), TT::Parameter, None);

        ControlFlow::Continue(())
    }

    fn visit_expr(&mut self, vcx: &VisitContext, expr: ExprIdx) -> ControlFlow<()> {
        let span = vcx.source_map.expr_span(expr);
        let e = vcx.cx.expr(expr);
        match &e.data {
            hir::ExprData::Literal(_) => {
                let tt = match &vcx.cx[vcx.cx.expr_ty(expr)] {
                    hir::TypeData::Function { .. } => TT::Function,
                    hir::TypeData::Primitive(_) => TT::Number,
                    hir::TypeData::Null => TT::Number,
                    _ => return ControlFlow::Continue(()),
                };

                self.push(span, tt, None);
            }
            hir::ExprData::Result => {
                self.push(span, TT::Keyword, None);
            }
            hir::ExprData::Struct { struct_span, .. } => {
                self.push(*struct_span, TT::Type, None);
            }
            hir::ExprData::If(it) => {
                if it.is_ghost {
                    self.inlay_hints.push(InlayHint {
                        position: Position::from_byte_offset(self.src, it.if_span.offset()),
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

    fn visit_ty(&mut self, vcx: &VisitContext, ty: hir::TypeSrcId) -> ControlFlow<()> {
        let ts = &vcx.cx[ty];
        match &vcx.cx[ts.ty] {
            hir::TypeData::Primitive(_) => {
                self.push_opt(
                    Some(vcx.source_map[ty].span()),
                    TT::Type,
                    Some(TM::DefaultLibrary),
                );
            }
            hir::TypeData::Struct(_) => {
                self.push_opt(Some(vcx.source_map[ty].span()), TT::Type, None);
            }
            _ => {}
        }

        ControlFlow::Continue(())
    }

    fn visit_stmt(&mut self, vcx: &VisitContext, stmt: &hir::Statement) -> ControlFlow<()> {
        if let hir::StatementData::Let {
            variable,
            explicit_ty,
            ..
        } = &stmt.data
        {
            if explicit_ty.is_none() {
                let span = vcx.cx.var_span(*variable);
                let ty = vcx.cx.var_ty(*variable);
                self.inlay_hints.push(InlayHint {
                    position: Position::from_byte_offset(self.src, span.end()),
                    label: format!(": {}", vcx.cx.pretty_ty(self.db, ty)),
                    kind: None,
                    padding_left: None,
                    padding_right: None,
                });
            }
        }

        ControlFlow::Continue(())
    }
}
