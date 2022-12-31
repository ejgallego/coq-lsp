import { basename } from "path";
import { Webview, Position, Uri, WebviewPanel } from "vscode";
import {
  RequestType,
  TextDocumentIdentifier,
  VersionedTextDocumentIdentifier,
} from "vscode-languageclient";
import { LanguageClient } from "vscode-languageclient/node";

interface Hyp {
  names: string;
  ty: string;
}
interface Goal {
  ty: string;
  hyps: Hyp[];
}

interface GoalRequest {
  textDocument: TextDocumentIdentifier;
  position: Position;
}

interface GoalAnswer {
  textDocument: VersionedTextDocumentIdentifier;
  position: Position;
  goals: Goal[];
}

function htmlOfHyp(hyp: Hyp) {
  let hypBody =
    `<label class="hname">${hyp.names}</label>` +
    `<label class="sep"> : </label>` +
    `<span class="htype">${hyp.ty}</span><br/>`;

  return `<div class="hypothesis"> ${hypBody} </div>`;
}
function htmlOfGoal(goal: Goal, idx: number) {
  let hyps = goal.hyps.map(htmlOfHyp).join(" ");
  let goalBody = `<div class="pp_goals"> <span class="goal">${goal.ty}</span><br/></div>`;
  let summary = `<summary>Goal ${idx}</summary>`;
  return (
    `<details ${idx == 0 ? "open" : "closed"}> ${summary}` +
    `<div class="goalDiv">${hyps} <hr/> ${goalBody} </div>` +
    `</details>`
  );
}

// returns the HTML code of goals environment
function htmlOfGoals(goals: Goal[]) {
  if (goals.length == 0) return "No goals";
  else return goals.map(htmlOfGoal).join("<br/>");
}

// Returns the HTML code of the panel and the inset ccontent
function buildGoalsContent(goals: GoalAnswer, styleUri: Uri) {
  // get the HTML code of goals environment
  let vsUri = Uri.parse(goals.textDocument.uri);
  let uriBase = basename(vsUri.path);
  let codeEnvGoals: String = htmlOfGoals(goals.goals);

  // Use #FA8072 color too?
  return `
    <!DOCTYPE html>
    <html lang="en">
    <head>
        <meta charset="UTF-8">
        <link rel="stylesheet" type="text/css" href="${styleUri}" >
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <title>Goals</title>
    </head>
    <body>
        <details open>
            <summary>${uriBase}:${goals.position.line}:${goals.position.character}</summary>
            <div class="goals_env" style="margin-left: 0.5ex;">
                ${codeEnvGoals}
            </div>
        </details>
    </body>
    </html>`;
}
// Goal View
class GoalView {
  private view: Webview;
  private client: LanguageClient;
  private styleUri: Uri;

  constructor(client: LanguageClient, view: Webview, styleUri: Uri) {
    this.view = view;
    this.client = client;
    this.styleUri = styleUri;
  }

  update(uri: Uri, position: Position) {
    this.sendGoalsRequest(uri, position);
  }

  display(goals: GoalAnswer) {
    this.view.html = buildGoalsContent(goals, this.styleUri);
  }

  // LSP Protocol extension for Goals
  sendGoalsRequest(uri: Uri, position: Position) {
    let doc = { uri: uri.toString() };
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

  constructor(client: LanguageClient, panel: WebviewPanel, styleUri: Uri) {
    this.panel = panel;
    this.view = new GoalView(client, panel.webview, styleUri);
  }
  update(uri: Uri, position: Position) {
    this.view.update(uri, position);
  }
  dispose() {
    this.panel.dispose();
  }
}
