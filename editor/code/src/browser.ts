import { ExtensionContext, Uri } from "vscode";
import { CancellationToken, LanguageClient, LanguageClientOptions, MessageSignature, NotificationType, NotificationType0, ProtocolNotificationType, ProtocolNotificationType0, ProtocolRequestType, ProtocolRequestType0, RequestType, RequestType0 } from "vscode-languageclient/browser";
import { activateCoqLSP, ClientFactoryType, deactivateCoqLSP } from "./client";

class InterruptibleLC extends LanguageClient {
  private readonly interrupt_vec?: Int32Array;

  constructor(id: string, name: string, clientOptions: LanguageClientOptions, worker: Worker) {
    super(id, name, clientOptions, worker);
    // We don't fail if COI is not enabled, as of Feb 2023 you must either:
    // - pass --enable-coi to vscode
    // - use `?enable-coi= in the vscode dev setup
    // See https://code.visualstudio.com/updates/v1_72#_towards-cross-origin-isolation
    // See https://github.com/microsoft/vscode-wasm
    if( typeof SharedArrayBuffer !== 'undefined' ) {
      this.interrupt_vec = new Int32Array(new SharedArrayBuffer(4));
      worker.postMessage(['SetupInterrupt', this.interrupt_vec]);
    }
  }

  public interrupt() {
    if(this.interrupt_vec) { Atomics.add(this.interrupt_vec, 0, 1); }
  }

  public sendRequest<R, PR, E, RO>(type: ProtocolRequestType0<R, PR, E, RO>, token?: CancellationToken): Promise<R>;
	public sendRequest<P, R, PR, E, RO>(type: ProtocolRequestType<P, R, PR, E, RO>, params: P, token?: CancellationToken): Promise<R>;
	public sendRequest<R, E>(type: RequestType0<R, E>, token?: CancellationToken): Promise<R>;
	public sendRequest<P, R, E>(type: RequestType<P, R, E>, params: P, token?: CancellationToken): Promise<R>;
	public sendRequest<R>(method: string, token?: CancellationToken): Promise<R>;
	public sendRequest<R>(method: string, param: any, token?: CancellationToken): Promise<R>;
  public async sendRequest<R>(type: string | MessageSignature, ...params: any[]): Promise<R> {
    this.interrupt();
    let ty = type as string;
    return super.sendRequest<R>(ty, ...params);
  }
  
  public sendNotification<RO>(type: ProtocolNotificationType0<RO>): Promise<void>;
	public sendNotification<P, RO>(type: ProtocolNotificationType<P, RO>, params?: P): Promise<void>;
	public sendNotification(type: NotificationType0): Promise<void>;
	public sendNotification<P>(type: NotificationType<P>, params?: P): Promise<void>;
	public sendNotification(method: string): Promise<void>;
	public sendNotification(method: string, params: any): Promise<void>;
	public async sendNotification<P>(type: string | MessageSignature, params?: P): Promise<void> {
    this.interrupt();
    let ty = type as NotificationType<P>;
    return super.sendNotification<P>(ty, params);
  }
}

export function activate(context: ExtensionContext): void {
  const cf: ClientFactoryType = (context, clientOptions, wsConfig) => {
    // Pending on having the API to fetch the worker file.
    // throw "Worker not found";
    const coqWorker = Uri.joinPath(context.extensionUri, "out/coq_lsp_worker.bc.js");
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
  activateCoqLSP(context, cf);
}

export function deactivate() {
  deactivateCoqLSP();
}