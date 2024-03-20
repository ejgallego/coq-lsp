import {
  Position,
  Uri,
  WebviewPanel,
  window,
  ViewColumn,
  extensions,
  commands,
} from "vscode";
import {
  BaseLanguageClient,
  RequestType,
  VersionedTextDocumentIdentifier,
} from "vscode-languageclient";
import { GoalRequest, GoalAnswer, PpString } from "../lib/types";

export const goalReq = new RequestType<GoalRequest, GoalAnswer<PpString>, void>(
  "proof/goals"
);

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
  postMessage(method: string, params: any) {
    this.ensurePanel();
    this.panel?.webview.postMessage({ method, params });
  }
  // notify the display that we are waiting for info
  requestSent(cursor: GoalRequest) {
    this.postMessage("waitingForInfo", cursor);
  }

  // notify the info panel that we have fresh goals to render
  requestDisplay(goals: GoalAnswer<PpString>) {
    this.postMessage("renderGoals", goals);
  }

  requestVizxDisplay(goals: GoalAnswer<PpString>) {
    console.log(goals);
    commands.executeCommand("vizx.lspRender", goals);
  }

    requestVizCarDisplay(goals: GoalAnswer<PpString>) {
    console.log(goals);
    commands.executeCommand("vizcar.lspRender", goals);
  }


  // notify the info panel that we found an error
  requestError(e: any) {
    this.postMessage("infoError", e);
  }

  // LSP Protocol extension for Goals
  sendGoalsRequest(client: BaseLanguageClient, params: GoalRequest) {
    this.requestSent(params);
    client.sendRequest(goalReq, params).then(
      (goals) => this.requestDisplay(goals),
      (reason) => this.requestError(reason)
    );
  }

  sendVizxRequest(client: BaseLanguageClient, params: GoalRequest) {
    this.requestSent(params);
    console.log(params.pp_format);
    client.sendRequest(goalReq, params).then(
      (goals) => this.requestVizxDisplay(goals),
      (reason) => this.requestError(reason)
    );
  }

  sendVizCarRequest(client: BaseLanguageClient, params: GoalRequest) {
    this.requestSent(params);
    console.log(params.pp_format);
    client.sendRequest(goalReq, params).then(
      (goals) => this.requestVizCarDisplay(goals),
      (reason) => this.requestError(reason)
    );
  }

  updateFromServer(
    client: BaseLanguageClient,
    uri: Uri,
    version: number,
    position: Position
  ) {
    let textDocument = VersionedTextDocumentIdentifier.create(
      uri.toString(),
      version
    );
    // let pretac = "idtac.";
    // let cursor: GoalRequest = { textDocument, position, pretac };
    let cursor: GoalRequest = { textDocument, position };
    let strCursor: GoalRequest = {
      textDocument,
      position,
      pp_format: "Str",
    };
    this.sendGoalsRequest(client, cursor);
    let vizx = extensions.getExtension("inQWIRE.vizx");
    if (vizx?.isActive) {
      console.log("vizx active in updateFromServer");
      this.sendVizxRequest(client, strCursor);
    }
    let vizcar = extensions.getExtension("inQWIRE.vizcar");
    if (vizcar?.isActive) {
      console.log("vizcar active in updateFromServer");
      this.sendVizCarRequest(client, strCursor);
    }
  }
}
