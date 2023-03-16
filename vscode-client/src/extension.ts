import { commands, ExtensionContext, Uri, workspace, window } from "vscode";

import {
  Disposable,
  Executable,
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from "vscode-languageclient/node";

let client: LanguageClient;

export async function activate(context: ExtensionContext) {
  let disposable = commands.registerCommand(
    "helloworld.helloWorld",
    async (uri) => {
      // The code you place here will be executed every time your command is executed
      // Display a message box to the user
      const url = Uri.parse(
        "/home/victor/Documents/test-dir/mist/another.mist"
      );
      let document = await workspace.openTextDocument(uri);
      await window.showTextDocument(document);

      // let editor = window.activeTextEditor;
      // let range = new Range(1, 1, 1, 1);
      // editor.selection = new Selection(range.start, range.end);
    }
  );

  context.subscriptions.push(disposable);

  const traceOutputChannel = window.createOutputChannel(
    "Mist Language Server trace"
  );
  const command = process.env.SERVER_PATH || "mist-lsp";
  const run: Executable = {
    command,
    options: {
      env: {
        ...process.env,
        RUST_LOG: "debug",
      },
    },
  };
  const serverOptions: ServerOptions = {
    run,
    debug: run,
  };
  // If the extension is launched in debug mode then the debug server options are used
  // Otherwise the run options are used
  // Options to control the language client
  let clientOptions: LanguageClientOptions = {
    // Register the server for plain text documents
    documentSelector: [{ scheme: "file", language: "mist" }],
    synchronize: {
      // Notify the server about file changes to '.clientrc files contained in the workspace
      fileEvents: workspace.createFileSystemWatcher("**/.clientrc"),
    },
    traceOutputChannel,
  };

  // Create the language client and start the client.
  client = new LanguageClient(
    "mist-lsp",
    "Mist language server",
    serverOptions,
    clientOptions
  );
  // activateInlayHints(context);
  client.start();
}
