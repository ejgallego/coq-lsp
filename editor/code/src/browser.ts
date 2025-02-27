import { ExtensionContext, Uri } from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
} from "vscode-languageclient/browser";
import {
  activateCoqLSP,
  ClientFactoryType,
  CoqLspAPI,
  deactivateCoqLSP,
} from "./client";
import { workspace } from "vscode";

class InterruptibleLC extends LanguageClient {
  private readonly interrupt_vec?: Int32Array;

  constructor(
    id: string,
    name: string,
    clientOptions: LanguageClientOptions,
    worker: Worker
  ) {
    super(id, name, clientOptions, worker);

    // We don't fail if COI is not enabled, as of Feb 2023 you must either:
    // - pass --enable-coi to vscode
    // - use `?enable-coi= in the vscode dev setup
    // See https://code.visualstudio.com/updates/v1_72#_towards-cross-origin-isolation
    // See https://github.com/microsoft/vscode-wasm
    if (typeof SharedArrayBuffer !== "undefined") {
      this.interrupt_vec = new Int32Array(new SharedArrayBuffer(4));
      worker.postMessage(["SetupInterrupt", this.interrupt_vec]);
    }

    this.middleware.sendRequest = (type, param, token, next) => {
      this.interrupt();
      return next(type, param, token);
    };
    this.middleware.sendNotification = (type, next, params) => {
      this.interrupt();
      return next(type, params);
    };

    this.middleware.didChange = (data, next) => {
      this.interrupt();
      return next(data);
    };
  }

  public interrupt() {
    if (this.interrupt_vec) {
      Atomics.add(this.interrupt_vec, 0, 1);
    }
  }
}

export function activate(context: ExtensionContext): CoqLspAPI {
  const cf: ClientFactoryType = (context, clientOptions, wsConfig) => {
    // Pending on having the API to fetch the worker file.
    // throw "Worker not found";
    const coqWorker = Uri.joinPath(
      context.extensionUri,
      "out/coq_lsp_worker.bc.js"
    );
    console.log(coqWorker);

    let worker = new Worker(coqWorker.toString(true));
    let client = new InterruptibleLC(
      "coq-lsp",
      "Coq LSP Worker",
      clientOptions,
      worker
    );
    return client;
  };

  // let files = Uri.joinPath(context.extensionUri, "out/files.json");

  // workspace.fs.readFile(files).then((content) => {
  //   let s = new TextDecoder().decode(content);
  //   console.log(`files: `, JSON.parse(s));
  // });

  return activateCoqLSP(context, cf);
}

export function deactivate() {
  deactivateCoqLSP();
}
