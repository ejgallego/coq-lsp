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
      console.log("interrupt requested (InterruptibleLC)");
      Atomics.add(this.interrupt_vec, 0, 1);
    }
  }
}

export function activate(context: ExtensionContext): CoqLspAPI {
  const cf: ClientFactoryType = (context, clientOptions, wsConfig) => {
    // Pending on having the API to fetch the worker file.
    // throw "Worker not found";

    let wasm = true;

    let workerURL = wasm
      ? "controller-wasm/out/wacoq_worker.js"
      : "out/coq_lsp_worker.bc.js";

    const coqWorker = Uri.joinPath(context.extensionUri, workerURL);

    console.log(coqWorker);

    // pass the init path to the worker
    let worker = new Worker(coqWorker.toString(true));
    worker.postMessage(context.extensionUri.toString());

    // send core fs (loaded worker side due to async)
    // let core_fs_uri = Uri.joinPath(context.extensionUri, "controller-wasm/out/core-fs.zip");
    // worker.postMessage(["LoadPkg", core_fs_uri.toString()]);

    let client = new InterruptibleLC(
      "coq-lsp",
      "Coq LSP Worker",
      clientOptions,
      worker
    );
    // let client = new LanguageClient(
    //   "coq-lsp",
    //   "Coq LSP Worker",
    //   clientOptions,
    //   worker
    // );
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
