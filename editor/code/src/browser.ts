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
  private readonly debug_int: boolean = false;
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
    if (typeof SharedArrayBuffer !== "undefined") {
      console.log("Interrupt Setup Requested (client)");
      this.interrupt_vec = new Int32Array(new SharedArrayBuffer(4));
      worker.postMessage(["InterruptSetup", this.interrupt_vec]);
    } else {
      console.log("Interrupt Setup Failed (client)");
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
      if (this.debug_int) console.log("interrupt requested (InterruptibleLC)");
      Atomics.add(this.interrupt_vec, 0, 1);
    }
  }
}

export function activate(context: ExtensionContext): CoqLspAPI {
  const cf: ClientFactoryType = (context, clientOptions, wsConfig) => {
    // Pending on having the API to fetch the worker file.
    // throw "Worker not found";

    let wasm = true;

    // TODO [WASM]: allow to retrieve wacoq_worker.bc in compressed form
    let workerURL = wasm
      ? "wasm-bin/wacoq_worker.js"
      : "out/coq_lsp_worker.bc.js";

    const coqWorker = Uri.joinPath(context.extensionUri, workerURL);

    // pass the init path to the worker
    let worker = new Worker(coqWorker.toString(true));

    // WASM needs the URI to initialize Rocq
    if (wasm) worker.postMessage(context.extensionUri.toString());

    let client = new InterruptibleLC(
      "coq-lsp",
      "Coq LSP Worker",
      clientOptions,
      worker
    );

    return client;
  };

  return activateCoqLSP(context, cf);
}

export function deactivate() {
  deactivateCoqLSP();
}
