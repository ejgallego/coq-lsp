import * as cp from "child_process";
import * as os from "os";
import * as path from "path";
import * as rpc from "vscode-jsonrpc/node";
import * as Protocol from "vscode-languageserver-protocol";
import { URI } from "vscode-uri";

let serverBin = os.platform() === "win32" ? "coq-lsp.exe" : "coq-lsp";

let serverPath = path.join(
  __dirname,
  "..",
  "..",
  "_build",
  "install",
  "default",
  "bin",
  serverBin
);

export type LanguageServer = rpc.MessageConnection;

export function toURI(s: string) {
  return URI.parse(s).toString();
}

export function start() {
  let childProcess = cp.spawn(serverPath);
  let connection = rpc.createMessageConnection(
    new rpc.StreamMessageReader(childProcess.stdout!),
    new rpc.StreamMessageWriter(childProcess.stdin!)
  );
  connection.listen();

  return connection as LanguageServer;
}

export async function startAndInitialize(
  initializeParameters: Partial<Protocol.InitializeParams> = {}
) {
  let languageServer = start();

  initializeParameters = {
    processId: process.pid,
    rootUri: toURI(path.join(__dirname, "..", "..")),
    workspaceFolders: [],
    capabilities: {
      textDocument: {
        publishDiagnostics: {
          relatedInformation: true,
        },
      },
    },
    ...initializeParameters,
  };

  await languageServer.sendRequest(
    Protocol.InitializeRequest.type,
    initializeParameters
  );
  return languageServer;
}

export async function exit(languageServer: LanguageServer) {
  await languageServer.sendNotification(Protocol.ExitNotification.type);
  return new Promise((resolve) => {
    languageServer.onClose(() => resolve(languageServer.dispose()));
  });
}
