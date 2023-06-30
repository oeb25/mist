mod tokens;

use std::{ops::ControlFlow, sync::Arc};

use derive_new::new;
use itertools::Itertools;
use mist_core::{
    file::SourceFile,
    hir::{self, ExprIdx, TypeRefKind, VariableIdx},
    mir::{self, pass::Pass},
    mono::{self, types::Type},
    salsa,
    types::{TypeProvider, TDK},
    util::Position,
    visit::{PostOrderWalk, VisitContext, Visitor, Walker},
};
use mist_syntax::{
    ast::{self, Spanned},
    AstNode, SourceSpan,
};
pub use tokens::{TokenModifier, TokenType};
use tower_lsp::lsp_types::{self, SemanticToken};

#[allow(unused)]
use TokenModifier as TM;
use TokenType as TT;

#[salsa::tracked]
pub fn highlighting(db: &dyn crate::Db, file: SourceFile) -> Arc<HighlightResult> {
    let root = file.root(db);
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
        mono::monomorphized_items(db, source)
            .items(db)
            .into_iter()
            .filter_map(|item| {
                let mir = mir::lower_item(db, item)?;
                let mir_source_map = mir.source_map(db);
                let mut ib = mir.ib(db).clone();
                mir::pass::FullDefaultPass::run(db, &mut ib);

                let cfg = mir::analysis::cfg::Cfg::compute(db, &ib);
                for entry in ib.entry_blocks() {
                    cfg.visit_reverse_post_order(entry, |bid| {
                        let mut stacked_up = vec![];
                        for inst in bid.locations(&ib).filter_map(|loc| loc.as_instruction()) {
                            if let mir::Instruction::Folding(f) = inst.data(&ib) {
                                stacked_up.push(f)
                            }

                            let Some(expr) = mir_source_map.trace_expr(inst) else { continue };

                            for f in stacked_up.drain(..) {
                                let p = mir::serialize::serialize_place(
                                    mir::serialize::Color::No,
                                    db,
                                    &ib,
                                    f.place(),
                                );
                                result.push(InlayHint {
                                    position: Position::from_byte_offset(
                                        source.text(db),
                                        expr.ast(db).span().offset(),
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
        use mist_core::VariableDeclarationKind as VDK;

        let decl = vcx.cx.decl(var);
        let tt = match decl.kind() {
            VDK::Let { .. } => TT::Variable,
            VDK::Parameter => TT::Parameter,
            VDK::Function(_) => TT::Function,
            VDK::Undefined => return ControlFlow::Continue(()),
        };
        self.push(span, tt, None);

        if let Some(None) =
            decl.ast_name_or_name_ref(self.root).syntax().ancestors().find_map(|ast| {
                None.or_else(|| ast::Param::cast(ast.clone()).map(|p| p.ty()))
                    .or_else(|| ast::LetStmt::cast(ast).map(|l| l.ty()))
            })
        {
            if let ast::NameOrNameRef::Name(_) = decl.ast_name_or_name_ref(self.root) {
                let ty = vcx.cx.var_ty(self.db, var);
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

    fn visit_expr(&mut self, vcx: &VisitContext, expr: ExprIdx) -> ControlFlow<()> {
        let src = vcx.source_map.expr_src(&vcx.cx, expr);
        let e = vcx.cx.original_expr(expr);
        match &e.data {
            hir::ExprData::Literal(_) => {
                let tt = match vcx.cx.ty_data(vcx.cx.expr_ty(expr)).kind {
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
            hir::ExprData::Adt { .. } => {
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

    fn visit_ty(&mut self, vcx: &VisitContext, ts: hir::TypeSrc, _ty: Type) -> ControlFlow<()> {
        match ts.type_ref(self.db) {
            Some(TypeRefKind::Primitive(_)) => {
                self.push_opt(Some(vcx.source_map[ts].span()), TT::Type, Some(TM::DefaultLibrary));
            }
            Some(TypeRefKind::Path(_)) => {
                self.push_opt(Some(vcx.source_map[ts].span()), TT::Type, None);
            }
            _ => {}
        }

        ControlFlow::Continue(())
    }
}
