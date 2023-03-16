use tower_lsp::jsonrpc::Result;
use tower_lsp::{LspService, Server};

use mist_lsp::backend::Backend;

#[tokio::main]
async fn main() -> Result<()> {
    miette::set_panic_hook();

    run().await?;

    Ok(())
}

async fn run() -> Result<()> {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(Backend::new);
    Server::new(stdin, stdout, socket).serve(service).await;

    Ok(())
}
