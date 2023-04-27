use tower_lsp::jsonrpc::Result;
use tower_lsp::{LspService, Server};

use mist_lsp::backend::Backend;

#[tokio::main(flavor = "current_thread")]
async fn main() -> Result<()> {
    miette::set_panic_hook();

    let local = tokio::task::LocalSet::new();

    // Run the local task set.
    local
        .run_until(async move {
            run().await.unwrap();
        })
        .await;

    Ok(())
}

async fn run() -> Result<()> {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| Backend::new(client).unwrap());
    Server::new(stdin, stdout, socket).serve(service).await;

    Ok(())
}
