import { Webview, Position, Uri, WebviewPanel } from "vscode";
import { RequestType } from "vscode-languageclient";
import { LanguageClient } from "vscode-languageclient/node";
import { GoalRequest, GoalAnswer } from "../lib/types";

// Goal View
class GoalView {
  private view: Webview;
  private client: LanguageClient;
  private styleUri: Uri;
  private scriptUri: Uri;

  constructor(
    client: LanguageClient,
    view: Webview,
    styleUri: Uri,
    scriptUri: Uri
  ) {
    this.view = view;
    this.client = client;
    this.styleUri = styleUri;
    this.scriptUri = scriptUri;
    this.view.html = ` <!DOCTYPE html>
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
  }

  update(uri: Uri, version: number, position: Position) {
    this.sendGoalsRequest(uri, version, position);
  }

  display(goals: GoalAnswer) {
    this.view.postMessage({ method: "renderGoals", params: goals });
  }

  // LSP Protocol extension for Goals
  sendGoalsRequest(uri: Uri, version: number, position: Position) {
    let doc = { uri: uri.toString(), version };
    let cursor: GoalRequest = { textDocument: doc, position: position };
    const req = new RequestType<GoalRequest, GoalAnswer, void>("proof/goals");
    this.client.sendRequest(req, cursor).then(
      (goals) => this.display(goals),
      () => {
        console.log("goal request failed!");
      }
    );
  }
}

export class GoalPanel {
  private view: GoalView;
  private panel: WebviewPanel;

  constructor(
    client: LanguageClient,
    panel: WebviewPanel,
    styleUri: Uri,
    scriptUri: Uri
  ) {
    this.panel = panel;
    this.view = new GoalView(client, panel.webview, styleUri, scriptUri);
  }
  update(uri: Uri, version: number, position: Position) {
    this.view.update(uri, version, position);
  }
  dispose() {
    this.panel.dispose();
  }
}
