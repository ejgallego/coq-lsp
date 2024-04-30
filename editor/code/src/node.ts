import { ExtensionContext } from "vscode";
import { LanguageClient, ServerOptions } from "vscode-languageclient/node";
import {
  activateCoqLSP,
  ClientFactoryType,
  CoqLspAPI,
  deactivateCoqLSP,
} from "./client";

export function activate(context: ExtensionContext): CoqLspAPI {
  const cf: ClientFactoryType = (context, clientOptions, wsConfig) => {
    const serverOptions: ServerOptions = {
      command: wsConfig.path,
      args: wsConfig.args,
    };
    return new LanguageClient(
      "coq-lsp",
      "Coq LSP Server",
      serverOptions,
      clientOptions
    );
  };
  return activateCoqLSP(context, cf);
}

export function deactivate() {
  return deactivateCoqLSP();
}
