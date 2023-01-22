import {
  Position,
  Uri,
  WebviewPanel,
  window,
  WebviewOptions,
  ViewColumn,
} from "vscode";
import {
  RequestType,
  VersionedTextDocumentIdentifier,
} from "vscode-languageclient";
import { LanguageClient } from "vscode-languageclient/node";
import { GoalRequest, GoalAnswer } from "../lib/types";

const infoReq = new RequestType<GoalRequest, GoalAnswer, void>("proof/goals");

export class InfoPanel {
  private panel: WebviewPanel | null = null;
  private extensionUri: Uri;

  constructor(extensionUri: Uri) {
    this.extensionUri = extensionUri;
    this.panelFactory();
  }

  dispose() {
    this.panel?.dispose();
  }

  panelFactory() {
    let webviewOpts: WebviewOptions = { enableScripts: true };
    this.panel = window.createWebviewPanel(
      "goals",
      "Goals",
      ViewColumn.Two,
      webviewOpts
    );

    const styleUri = this.panel.webview.asWebviewUri(
      Uri.joinPath(this.extensionUri, "out", "view", "index.css")
    );

    const scriptUri = this.panel.webview.asWebviewUri(
      Uri.joinPath(this.extensionUri, "out", "view", "index.js")
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
    <div id="coq-info-body">
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
  postMessage(method: string, params: any) {
    this.ensurePanel();
    this.panel?.webview.postMessage({ method, params });
  }
  // notify the display that we are waiting for info
  requestSent(cursor: GoalRequest) {
    this.postMessage("waitingForInfo", cursor);
  }

  // notify the info panel that we have fresh goals to render
  requestDisplay(goals: GoalAnswer) {
    this.postMessage("renderGoals", goals);
  }

  // notify the info panel that we found an error
  requestError(e: any) {
    this.postMessage("infoError", e);
  }

  // LSP Protocol extension for Goals
  sendGoalsRequest(client: LanguageClient, params: GoalRequest) {
    this.requestSent(params);
    client.sendRequest(infoReq, params).then(
      (goals) => this.requestDisplay(goals),
      (reason) => this.requestError(reason)
    );
  }

  updateFromServer(
    client: LanguageClient,
    uri: Uri,
    version: number,
    position: Position
  ) {
    let textDocument = VersionedTextDocumentIdentifier.create(
      uri.toString(),
      version
    );
    let cursor: GoalRequest = { textDocument, position };
    this.sendGoalsRequest(client, cursor);
  }
}
