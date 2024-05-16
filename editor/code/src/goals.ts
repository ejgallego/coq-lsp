import {
  Uri,
  WebviewPanel,
  window,
  ViewColumn,
  extensions,
  commands,
  TextDocument,
} from "vscode";
import {
  BaseLanguageClient,
  RequestType,
  ResponseError,
  VersionedTextDocumentIdentifier,
} from "vscode-languageclient";
import {
  GoalRequest,
  GoalAnswer,
  PpString,
  CoqMessagePayload,
  ErrorData,
} from "../lib/types";

import {
  URI,
  Position,
  TextDocumentIdentifier,
} from "vscode-languageserver-types";

export const goalReq = new RequestType<GoalRequest, GoalAnswer<PpString>, void>(
  "proof/goals"
);

export class InfoPanel {
  private panel: WebviewPanel | null = null;
  private extensionUri: Uri;
  private listeners: Array<(goals: GoalAnswer<String>) => void> = [];

  constructor(extensionUri: Uri) {
    this.extensionUri = extensionUri;
    this.panelFactory();
  }

  dispose() {
    this.panel?.dispose();
  }

  registerObserver(fn: (goals: GoalAnswer<String>) => void) {
    this.listeners.push(fn);
  }

  unregisterObserver(fn: (goals: GoalAnswer<String>) => void) {
    let index = this.listeners.indexOf(fn);
    if (index >= 0) {
      this.listeners.splice(index, 1);
    }
  }

  panelFactory() {
    let webviewOpts = { enableScripts: true, enableFindWidget: true };
    this.panel = window.createWebviewPanel(
      "goals",
      "Goals",
      { preserveFocus: true, viewColumn: ViewColumn.Two },
      webviewOpts
    );

    const styleUri = this.panel.webview.asWebviewUri(
      Uri.joinPath(this.extensionUri, "out", "views", "info", "index.css")
    );

    const scriptUri = this.panel.webview.asWebviewUri(
      Uri.joinPath(this.extensionUri, "out", "views", "info", "index.js")
    );

    this.panel.webview.html = ` <!DOCTYPE html>
    <html lang="en">
    <head>
        <meta charset="UTF-8">
        <link rel="stylesheet" type="text/css" href="${styleUri}">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <script src="${scriptUri}" type="module"></script>
        <title>Coq's info panel</title>
    </head>
    <body>
    <div id="root">
    </div>
    </body>
    </html>`;

    // The panel was closed by the user, guard!
    this.panel.onDidDispose(() => {
      this.panel = null;
    });
  }

  ensurePanel() {
    if (!this.panel) {
      this.panelFactory();
    }
  }
  postMessage({ method, params }: CoqMessagePayload) {
    this.ensurePanel();
    this.panel?.webview.postMessage({ method, params });
  }

  // notify the display that we are waiting for info
  requestSent(cursor: GoalRequest) {
    this.postMessage({ method: "waitingForInfo", params: cursor });
  }

  // notify the info panel that we have fresh goals to render
  requestDisplay(goals: GoalAnswer<PpString>) {
    this.postMessage({ method: "renderGoals", params: goals });
  }

  // notify the info panel that we found an error
  requestError(e: ErrorData) {
    this.postMessage({ method: "infoError", params: e });
  }

  notifyLackOfVSLS(
    textDocument: VersionedTextDocumentIdentifier,
    position: Position
  ) {
    let message =
      "Support for Goal Display is not available (yet) under Visual Studio Live Share";
    this.requestError({ textDocument, position, message });
  }

  // LSP Protocol extension for Goals
  updateInfoPanelForCursor(client: BaseLanguageClient, params: GoalRequest) {
    this.requestSent(params);
    client.sendRequest(goalReq, params).then(
      (goals) => this.requestDisplay(goals),
      (error: ResponseError<void>) => {
        let textDocument = params.textDocument;
        let position = params.position;
        let message = error.message;
        this.requestError({ textDocument, position, message });
      }
    );
  }

  updateAPIClientForCursor(client: BaseLanguageClient, params: GoalRequest) {
    if (this.listeners.length > 0) {
      params.pp_format = "Str";
      client.sendRequest(goalReq, params).then(
        (goals) => {
          let goals_fn = goals as GoalAnswer<String>;
          this.listeners.forEach((fn) => fn(goals_fn));
        },
        // We should actually provide a better setup so we can pass the rejection of the promise to our clients, YMMV tho.
        (reason) => this.requestError(reason)
      );
    }
  }

  // Protocol-level data
  updateFromServer(
    client: BaseLanguageClient,
    uri: URI,
    version: number,
    position: Position,
    pp_format: "Pp" | "Str"
  ) {
    let textDocument = VersionedTextDocumentIdentifier.create(uri, version);

    // Example to test the `command` parameter
    // let command = "idtac.";
    // let cursor: GoalRequest = { textDocument, position, command };
    let cursor: GoalRequest = { textDocument, position, pp_format };
    this.updateInfoPanelForCursor(client, cursor);
    this.updateAPIClientForCursor(client, cursor);
  }
}
