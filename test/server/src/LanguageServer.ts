import * as cp from "node:child_process";
import * as os from "node:os";
import * as path from "node:path";
import * as fs from "node:fs";
import * as rpc from "vscode-jsonrpc/node";
import * as Protocol from "vscode-languageserver-protocol";
import * as Types from "vscode-languageserver-types";
import { URI } from "vscode-uri";

let serverBin = os.platform() === "win32" ? "coq-lsp.exe" : "coq-lsp";
let projectRoot = path.join(__dirname, "..", "..", "..");

let _serverPath = path.join(
  projectRoot,
  "_build",
  "install",
  "default",
  "bin",
  serverBin,
);

let serverPath = "coq-lsp"

// let ocamlPath = path.join(projectRoot, "_build", "install", "default", "lib");

export function toURI(s: string) {
  return URI.parse(s).toString();
}

export function openExampleEphemeral(filename: string, contents: string) {
  let filepath = path.join(projectRoot, filename);
  return Types.TextDocumentItem.create(toURI(filepath), "coq", 0, contents);
}

export function openExample(filename: string) {
  let filepath = path.join(projectRoot, "examples", filename);
  return Types.TextDocumentItem.create(
    toURI(filepath),
    "coq",
    0,
    fs.readFileSync(filepath, "utf-8"),
  );
}

export interface LanguageServer extends rpc.MessageConnection {
  initialize(
    initializeParameters?: Partial<Protocol.InitializeParams>,
    root?: string
  ): Promise<void>;

  exit(): Promise<void>;
}

export function start(): LanguageServer {
  let childProcess = cp.spawn(serverPath, ['--int_backend=Mp', '--bt'], {
    env: {
      ...process.env,
      // OCAMLPATH: ocamlPath,
    },
  });
  let connection = rpc.createMessageConnection(
    new rpc.StreamMessageReader(childProcess.stdout!),
    new rpc.StreamMessageWriter(childProcess.stdin!),
  );
  connection.listen();

  const initialize = async (
    initializeParameters: Partial<Protocol.InitializeParams> = {},
    root : string = projectRoot,
  ) => {
    initializeParameters = {
      processId: process.pid,
      // workspaceFolders: [
      //   {
      //     uri: toURI(root),
      //     name: "coq-lsp",
      //   },
      // ],
      initializationOptions: { eager_diagnostics: false },
      capabilities: {
        textDocument: {
          publishDiagnostics: {
            relatedInformation: true,
          },
        },
      },
      ...initializeParameters,
    };

    const log = (message : string | any, data?: any) => {
      console.log(`${message} | ${data}`);
    };

    const tracer : rpc.Tracer = { log };

    connection.trace(rpc.Trace.Verbose, tracer);

    await connection.sendRequest(
      Protocol.InitializeRequest.type,
      initializeParameters,
    );
  };

  const exit = async () => {
    await connection.sendNotification(Protocol.ExitNotification.type);
    return new Promise<void>((resolve) => {
      connection.onClose(() => resolve(connection.dispose()));
    });
  };

  return { ...connection, initialize, exit };
}
