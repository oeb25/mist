use std::sync::Arc;

use itertools::Itertools;
use mist_core::hir::{Program, SourceProgram};
use mist_syntax::SourceSpan;
use mist_viper_backend::gen::ViperHints;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::request::{GotoDeclarationParams, GotoDeclarationResponse};
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer};

use crate::highlighting::{TokenModifier, TokenType};
use crate::hover::HoverElement;

#[derive(Debug)]
pub struct Backend {
    client: Client,
    // TODO: ATM we can't store a DB since it contains types which are not
    // Send+Sync. To fix this, we should get rid of those :)
    // db: crate::db::Database,
    files: dashmap::DashMap<Url, Arc<String>>,
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, ip: InitializeParams) -> Result<InitializeResult> {
        self.initialize(ip).await
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "server initialized! :)")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.did_open(params).await
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        self.did_change(params).await
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        self.semantic_tokens_full(params).await
    }

    async fn inlay_hint(&self, params: InlayHintParams) -> Result<Option<Vec<InlayHint>>> {
        self.inlay_hint(params).await
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        self.hover(params).await
    }

    async fn goto_declaration(
        &self,
        params: GotoDeclarationParams,
    ) -> Result<Option<GotoDeclarationResponse>> {
        self.goto_declaration(params).await
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        self.goto_definition(params).await
    }
}

impl Backend {
    pub fn new(client: Client) -> Self {
        use tracing_subscriber::prelude::*;

        #[derive(Clone)]
        struct ClientLogger {
            client: Client,
        }

        impl std::io::Write for ClientLogger {
            fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
                let s = std::str::from_utf8(buf).unwrap().to_string();

                let client = self.client.clone();
                tokio::spawn(async move {
                    client.log_message(MessageType::LOG, s).await;
                });

                Ok(buf.len())
            }

            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }

        let logger_client = ClientLogger {
            client: client.clone(),
        };
        tracing_subscriber::Registry::default()
            .with(
                tracing_subscriber::EnvFilter::builder()
                    .with_default_directive(tracing_subscriber::filter::LevelFilter::INFO.into())
                    .from_env_lossy(),
            )
            .with(
                tracing_subscriber::fmt::layer()
                    .with_target(false)
                    .without_time()
                    .with_ansi(false)
                    .with_writer(move || logger_client.clone()),
            )
            .with(tracing_subscriber::filter::FilterFn::new(|m| {
                !m.target().contains("salsa")
            }))
            .init();

        Self {
            client,
            files: Default::default(),
        }
    }

    async fn initialize(&self, _ip: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensOptions(
                        SemanticTokensOptions {
                            work_done_progress_options: WorkDoneProgressOptions {
                                work_done_progress: None,
                            },
                            legend: SemanticTokensLegend {
                                token_types: TokenType::all().map_into().collect(),
                                token_modifiers: TokenModifier::all().map_into().collect(),
                            },
                            full: Some(SemanticTokensFullOptions::Bool(true)),
                            range: None,
                        },
                    ),
                ),
                inlay_hint_provider: Some(OneOf::Left(true)),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                declaration_provider: Some(DeclarationCapability::Simple(true)),
                definition_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
            ..Default::default()
        })
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.update_text(params.text_document.uri, params.text_document.text)
            .await
            .expect("did_open");
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        self.update_text(
            params.text_document.uri,
            params.content_changes[0].text.clone(),
        )
        .await
        .expect("did_change");
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let db = self.db();
        let Some(source) = self.source_program(&db, params.text_document.uri) else {
            return Err(tower_lsp::jsonrpc::Error::invalid_request());
        };
        let tokens = crate::highlighting::semantic_tokens(&db, source);
        Ok(Some(SemanticTokensResult::Partial(
            SemanticTokensPartialResult {
                data: tokens.to_vec(),
            },
        )))
    }
    async fn inlay_hint(&self, params: InlayHintParams) -> Result<Option<Vec<InlayHint>>> {
        let db = self.db();
        let Some(source) = self.source_program(&db, params.text_document.uri) else {
            return Err(tower_lsp::jsonrpc::Error::invalid_request());
        };
        let inlay_hints = crate::highlighting::inlay_hints(&db, source);

        let program = mist_core::hir::parse_program(&db, source);
        let hints = mist_viper_backend::gen::viper_file::accumulated::<ViperHints>(&db, program);

        Ok(Some(
            inlay_hints
                .iter()
                .cloned()
                .chain(
                    hints
                        .into_iter()
                        .map(|hint| crate::highlighting::InlayHint {
                            position: mist_core::util::Position::from_byte_offset(
                                source.text(&db),
                                hint.span.end(),
                            ),
                            label: hint.viper,
                            kind: None,
                            padding_left: Some(true),
                            padding_right: None,
                        }),
                )
                .map_into()
                .collect(),
        ))
    }
    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let db = self.db();
        let TextDocumentPositionParams {
            text_document,
            position,
        } = params.text_document_position_params;
        let Some(source) = self.source_program(&db, text_document.uri) else {
            return Err(tower_lsp::jsonrpc::Error::invalid_request());
        };
        let src = source.text(&db);
        let pos = mist_core::util::Position::new(position.line, position.character);
        let Some(byte_offset) = pos.to_byte_offset(src) else {
            return Ok(None);
        };
        let Some(hover) = crate::hover::hover(&db, source, byte_offset) else { return Ok(None); };
        Ok(Some(Hover {
            contents: HoverContents::Array(
                hover
                    .contents
                    .into_iter()
                    .map(|el| match el {
                        HoverElement::String(value) => MarkedString::String(value),
                        HoverElement::Code(value) => MarkedString::LanguageString(LanguageString {
                            language: "mist".to_string(),
                            value,
                        }),
                    })
                    .collect(),
            ),
            range: hover.range.map(|span| span_to_range(src, span)),
        }))
    }
    async fn goto_declaration(
        &self,
        params: GotoDeclarationParams,
    ) -> Result<Option<GotoDeclarationResponse>> {
        let db = self.db();
        let result = self.definition_span(&db, params.text_document_position_params)?;
        Ok(result.map(|link| GotoDeclarationResponse::Link(vec![link])))
    }
    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let db = self.db();
        let result = self.definition_span(&db, params.text_document_position_params)?;
        Ok(result.map(|link| GotoDeclarationResponse::Link(vec![link])))
    }
}

impl Backend {
    pub fn db(&self) -> impl crate::Db {
        crate::db::Database::default()
    }

    fn source_program(&self, db: &dyn crate::Db, uri: Url) -> Option<SourceProgram> {
        let text = self.files.get(&uri)?;
        Some(SourceProgram::new(db, text.to_string()))
    }

    fn program(&self, db: &dyn crate::Db, uri: Url) -> Option<Program> {
        let source = self.source_program(db, uri)?;
        Some(mist_core::hir::parse_program(db, source))
    }

    async fn update_text(&self, uri: Url, source: String) -> Result<()> {
        let text = Arc::new(source);
        self.files.insert(uri.clone(), Arc::clone(&text));

        let errors = {
            let db = self.db();

            let source = mist_core::hir::SourceProgram::new(&db, text.to_string());
            let program = mist_core::hir::parse_program(&db, source);

            let parse_errors = program.errors(&db);
            let type_errors = crate::highlighting::semantic_tokens::accumulated::<
                mist_core::TypeCheckErrors,
            >(&db, source);
            let viper_errors = mist_viper_backend::gen::viper_file::accumulated::<
                mist_viper_backend::lower::ViperLowerErrors,
            >(&db, program);

            itertools::chain!(
                parse_errors.iter().cloned().map(miette::Error::new),
                type_errors.into_iter().map(miette::Error::new),
                viper_errors.into_iter().map(miette::Error::new),
            )
            .flat_map(|e| miette_to_diagnostic(&text, e))
            .collect()
        };

        self.client.publish_diagnostics(uri, errors, None).await;

        Ok(())
    }

    fn definition_span(
        &self,
        db: &dyn crate::Db,
        TextDocumentPositionParams {
            text_document,
            position,
        }: TextDocumentPositionParams,
    ) -> Result<Option<LocationLink>> {
        let Some(source) = self.source_program(db, text_document.uri.clone()) else {
            return Err(tower_lsp::jsonrpc::Error::invalid_request());
        };
        let src = source.text(db);
        let pos = mist_core::util::Position::new(position.line, position.character);
        let Some(byte_offset) = pos.to_byte_offset(src) else {
            return Ok(None);
        };
        let Some(result) = crate::goto::goto_declaration(db, source, byte_offset) else { return Ok(None); };
        let target_range = span_to_range(src, result.target_span);
        Ok(Some(LocationLink {
            origin_selection_range: Some(span_to_range(src, result.original_span)),
            target_uri: text_document.uri,
            target_range,
            target_selection_range: target_range,
        }))
    }
}

fn span_to_range(src: &str, span: SourceSpan) -> Range {
    use mist_core::util::Position as Pos;

    let start = Pos::from_byte_offset(src, span.offset());
    let end = Pos::from_byte_offset(src, span.end());
    let start = Position::new(start.line, start.character);
    let end = Position::new(end.line, end.character);
    Range::new(start, end)
}

fn miette_to_diagnostic(src: &str, report: miette::Report) -> Vec<Diagnostic> {
    report
        .labels()
        .unwrap_or_else(|| Box::new(vec![].into_iter()))
        .map(|label| {
            use mist_core::util::Position as Pos;

            let start = Pos::from_byte_offset(src, label.offset());
            let end = Pos::from_byte_offset(src, label.offset() + label.len());
            let start = Position::new(start.line, start.character);
            let end = Position::new(end.line, end.character);
            let range = Range::new(start, end);
            Diagnostic {
                severity: Some(DiagnosticSeverity::ERROR),
                message: report.to_string(), // label.label().unwrap_or("here").to_string(),
                range,
                ..Default::default()
            }
        })
        .collect()
}
