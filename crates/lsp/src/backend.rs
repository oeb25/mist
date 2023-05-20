use std::{
    path::PathBuf,
    sync::{Arc, Mutex},
};

use dashmap::DashMap;
use itertools::Itertools;
use miette::IntoDiagnostic;
use mist_core::{
    hir::SourceProgram,
    salsa::{ParallelDatabase, Snapshot},
};
use mist_syntax::{ast::Spanned, SourceSpan};
use mist_viper_backend::gen::ViperHints;
use tower_lsp::{
    jsonrpc::Result,
    lsp_types::{
        request::{GotoDeclarationParams, GotoDeclarationResponse},
        *,
    },
    Client, LanguageServer,
};
use tracing::{error, info};

use crate::highlighting::{TokenModifier, TokenType};
use crate::hover::HoverElement;

pub struct Backend {
    client: Client,
    db: Arc<Mutex<crate::db::Database>>,
    files: DashMap<Url, Arc<String>>,
    working_dir: PathBuf,
    viper_server: Arc<Mutex<Option<viperserver::ViperServer>>>,

    verification_requests: DashMap<Url, tokio::task::JoinHandle<()>>,
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
    pub fn new(client: Client) -> miette::Result<Self> {
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
                    && !m.target().contains("ena")
                    && !m.target().contains("hyper")
                    && !m.target().contains("reqwest")
            }))
            .init();

        let target_dir = PathBuf::from("./.mist");
        let lsp_dir = target_dir.join("lsp");
        std::fs::create_dir_all(&lsp_dir).into_diagnostic()?;

        Ok(Self {
            client,
            db: Default::default(),
            files: Default::default(),
            working_dir: lsp_dir.canonicalize().into_diagnostic()?,
            viper_server: Default::default(),
            verification_requests: Default::default(),
        })
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
        self.update_text(
            params.text_document.uri,
            params.text_document.text,
            params.text_document.version,
        )
        .await
        .expect("did_open");
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        self.update_text(
            params.text_document.uri,
            params.content_changes[0].text.clone(),
            params.text_document.version,
        )
        .await
        .expect("did_change");
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let db = &*self.db();
        let Some(source) = self.source_program(db, params.text_document.uri) else {
            return Err(tower_lsp::jsonrpc::Error::invalid_request());
        };
        let tokens = crate::highlighting::semantic_tokens(db, source);
        Ok(Some(SemanticTokensResult::Partial(
            SemanticTokensPartialResult {
                data: tokens.to_vec(),
            },
        )))
    }
    async fn inlay_hint(&self, params: InlayHintParams) -> Result<Option<Vec<InlayHint>>> {
        let db = &*self.db();
        let Some(source) = self.source_program(db, params.text_document.uri) else {
            return Err(tower_lsp::jsonrpc::Error::invalid_request());
        };
        let inlay_hints = crate::highlighting::inlay_hints(db, source);

        let program = mist_core::hir::parse_program(db, source);
        let hints = mist_viper_backend::gen::viper_file::accumulated::<ViperHints>(db, program);

        Ok(Some(
            inlay_hints
                .iter()
                .cloned()
                .chain(
                    hints
                        .into_iter()
                        .map(|hint| crate::highlighting::InlayHint {
                            position: mist_core::util::Position::from_byte_offset(
                                source.text(db),
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
        let db = &*self.db();
        let TextDocumentPositionParams {
            text_document,
            position,
        } = params.text_document_position_params;
        let Some(source) = self.source_program(db, text_document.uri) else {
            return Err(tower_lsp::jsonrpc::Error::invalid_request());
        };
        let src = source.text(db);
        let pos = mist_core::util::Position::new(position.line, position.character);
        let Some(byte_offset) = pos.to_byte_offset(src) else {
            return Ok(None);
        };
        let Some(hover) = crate::hover::hover(db, source, byte_offset) else { return Ok(None); };
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
        let result = self.definition_span(&*self.db(), params.text_document_position_params)?;
        Ok(result.map(|link| GotoDeclarationResponse::Link(vec![link])))
    }
    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let db = &*self.db();
        let result = self.definition_span(db, params.text_document_position_params)?;
        Ok(result.map(|link| GotoDeclarationResponse::Link(vec![link])))
    }
}

impl Backend {
    fn db(&self) -> Snapshot<crate::db::Database> {
        self.db.lock().unwrap().snapshot()
    }

    fn source_program(&self, db: &dyn crate::Db, uri: Url) -> Option<SourceProgram> {
        let text = self.files.get(&uri)?;
        Some(SourceProgram::new(db, text.to_string()))
    }

    async fn update_text(&self, uri: Url, source: String, version: i32) -> Result<()> {
        let start = std::time::Instant::now();

        let text = Arc::new(source);
        self.files.insert(uri.clone(), Arc::clone(&text));

        let working_dir = self.working_dir.clone();
        let client = self.client.clone();
        let viperserver_jar = self.viperserver_jar();
        let viperserver_ref = Arc::clone(&self.viper_server);
        let task_uri = uri.clone();

        let db_arc = Arc::clone(&self.db);
        let join_handle = tokio::task::spawn(async move {
            let db = db_arc.lock().unwrap().snapshot();
            let uri = task_uri;

            let source = mist_core::hir::SourceProgram::new(&*db, text.to_string());
            let program = mist_core::hir::parse_program(&*db, source);
            let parse = program.parse(&*db).clone();

            let errors = mist_cli::accumulated_errors(&*db, program)
                .flat_map(|e| miette_to_diagnostic(&text, e.inner_diagnostic().unwrap()))
                .collect_vec();

            // drop(db);

            if errors.is_empty() {
                client
                    .publish_diagnostics(uri.clone(), vec![], Some(version))
                    .await;

                let viperserver = viperserver_ref.lock().unwrap().take();
                let viperserver = if let Some(it) = viperserver {
                    info!("reusing viperserver!");
                    it
                } else {
                    viperserver::server::ViperServer::builder()
                        .spawn_http(&viperserver_jar)
                        .await
                        .into_diagnostic()
                        .unwrap()
                };

                let verification_start = std::time::Instant::now();

                let verify_file = crate::viper::VerifyFile {
                    program,
                    viperserver_jar: &viperserver_jar,
                    viperserver: &viperserver,
                    working_dir: &working_dir,
                    mist_src_path: uri.as_str().into(),
                    mist_src: &text,
                };
                let errors = match verify_file.run(&db_arc).await {
                    Ok(errors) => errors,
                    Err(err) => vec![err],
                };

                *viperserver_ref.lock().unwrap() = Some(viperserver);

                let errors = errors
                    .into_iter()
                    .flat_map(|e| {
                        error!("verification error: {e:?}");

                        miette_to_diagnostic(&text, e)
                    })
                    .collect_vec();

                if errors.is_empty() {
                    client
                        .show_message(
                            MessageType::INFO,
                            format!(
                                "Successfully verified {} in {:?} + {:?}",
                                PathBuf::from(uri.as_str())
                                    .file_name()
                                    .unwrap()
                                    .to_string_lossy(),
                                verification_start.duration_since(start),
                                verification_start.elapsed()
                            ),
                        )
                        .await;

                    let diagnostics = program
                        .items(&*db)
                        .iter()
                        .map(|item| {
                            let span = item.syntax(&*db, &parse.tree()).span();
                            let range = span_to_range(&text, span.set_len(0));
                            Diagnostic {
                                severity: Some(DiagnosticSeverity::HINT),
                                message: "Successfully verified".to_string(),
                                range,
                                ..Default::default()
                            }
                        })
                        .collect();
                    client
                        .publish_diagnostics(uri.clone(), diagnostics, Some(version))
                        .await;
                } else {
                    client
                        .publish_diagnostics(uri.clone(), errors, Some(version))
                        .await;
                }
            } else {
                client.publish_diagnostics(uri, errors, Some(version)).await;
            }
        });

        if let Some(old) = self.verification_requests.insert(uri, join_handle) {
            old.abort();
        }

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

    fn viperserver_jar(&self) -> PathBuf {
        // TODO: do not hard code this
        PathBuf::from("/Users/oeb25/Projects/thesis/vipers/server/viperserver/target/scala-2.13/viperserver.jar")
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
    let diagnostics = report
        .labels()
        .map(|labels| {
            labels
                .map(|label| {
                    let range = span_to_range(
                        src,
                        SourceSpan::new_start_end(label.offset(), label.offset() + label.len()),
                    );
                    Diagnostic {
                        severity: Some(DiagnosticSeverity::ERROR),
                        message: report.to_string(), // label.label().unwrap_or("here").to_string(),
                        range,
                        ..Default::default()
                    }
                })
                .collect_vec()
        })
        .unwrap_or_default();

    if diagnostics.is_empty() {
        let severity = match report.severity() {
            Some(s) => todo!("{s:?}"),
            None => Some(DiagnosticSeverity::ERROR),
        };

        vec![Diagnostic {
            severity,
            message: report.to_string(),
            range: Range::new(Position::new(0, 0), Position::new(0, 0)),
            ..Default::default()
        }]
    } else {
        diagnostics
    }
}
