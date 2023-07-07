import { ExtensionContext } from "vscode";
import { LanguageClient, ServerOptions } from "vscode-languageclient/node";
import { activateCoqLSP, ClientFactoryType, deactivateCoqLSP } from "./client";

export function activate(context: ExtensionContext): void {
  const cf: ClientFactoryType = (context, clientOptions, wsConfig) => {
    const serverOptions: ServerOptions = {
      command: wsConfig.path,
      args: wsConfig.args,
    };
    return new LanguageClient(
      "coq-lsp",
      "Coq LSP Server",
      serverOptions,
      clientOptions,
    );
  };
  return activateCoqLSP(context, cf);
}

export function deactivate() {
  return deactivateCoqLSP();
}
