use std::sync::Arc;

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer};

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
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                ..Default::default()
            },
            ..Default::default()
        })
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
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Self {
            client,
            files: Default::default(),
        }
    }

    pub fn db(&self) -> impl crate::Db {
        crate::db::Database::default()
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
}

impl Backend {
    async fn update_text(&self, uri: Url, source: String) -> Result<()> {
        let text = Arc::new(source);
        self.files.insert(uri.clone(), Arc::clone(&text));

        let errors = {
            let db = crate::db::Database::default();

            let source = mist_core::ir::SourceProgram::new(&db, text.to_string());
            let program = mist_core::ir::parse_program(&db, source);

            let parse_errors = program.errors(&db);
            let type_errors = mist_viper_backend::gen::viper_file::accumulated::<
                mist_core::TypeCheckErrors,
            >(&db, program);

            itertools::chain!(
                parse_errors.iter().cloned().map(miette::Error::new),
                type_errors.into_iter().map(miette::Error::new),
            )
            .flat_map(|e| miette_to_diagnostic(&text, e))
            .collect()
        };

        self.client.publish_diagnostics(uri, errors, None).await;

        Ok(())
    }
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
                related_information: None,
                tags: None,
                range,
                code: None,
                code_description: None,
                source: None,
                data: None,
            }
        })
        .collect()
}
