import { ExtensionContext } from "vscode";
import { LanguageClient } from "vscode-languageclient/browser";
import { activateCoqLSP, ClientFactoryType, deactivateCoqLSP } from "./client";

export function activate(context: ExtensionContext): void {
  const cf: ClientFactoryType = (context, clientOptions, wsConfig) => {
    // Pending on having the API to fetch the worker file.
    throw "Worker not found";
    let worker = new Worker("");
    return new LanguageClient(
      "coq-lsp",
      "Coq LSP Worker",
      clientOptions,
      worker
    );
  };
  activateCoqLSP(context, cf);
}

export function deactivate() {
  deactivateCoqLSP();
}
