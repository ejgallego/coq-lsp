import { Webview, Position, Uri, WebviewPanel } from "vscode";
import { RequestType } from "vscode-languageclient";
import { LanguageClient } from "vscode-languageclient/node";

interface Hyp {
    names: string;
    ty: string;
}
interface Goal {
    ty: string;
    hyps: Hyp[];
}
interface GoalRequest {}

// returns the HTML code of goals environment
function getGoalsEnvContent(goals: Goal[]) {
    if (goals.length == 0) return "No goals";

    return goals
        .map((curGoal, itr) => {
            return (
                '<div class="hypothesis">' +
                curGoal.hyps
                    .map((hyp) => {
                        return (
                            `<label class="hname">${hyp.names}</label>` +
                            `<label class="sep"> : </label>` +
                            `<span class="htype">${hyp.ty}</span><br/>`
                        );
                    })
                    .reduce((acc, cur) => acc + cur, "") +
                "</div>" +
                "<hr/>" +
                `<div class="pp_goals">` +
                `<label class="numGoal">${itr}</label>` +
                `<label class="sep"> : </label>` +
                `<span class="goal">${curGoal.ty}</span>` +
                `<label class ="sep"></label><br/><br/>` +
                `</div>`
            );
        })
        .reduce((acc, cur) => acc + cur, "");
}

// Returns the HTML code of the panel and the inset ccontent
function buildGoalsContent(goals: Goal[], styleUri: Uri) {
    // get the HTML code of goals environment
    let codeEnvGoals: String = getGoalsEnvContent(goals);

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
        <p class="goals_env">
        ${codeEnvGoals}
        </p>
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

    display(goals: Goal[]) {
        this.view.html = buildGoalsContent(goals, this.styleUri);
    }

    // LSP Protocol extension for Goals
    sendGoalsRequest(uri: Uri, position: Position) {
        let doc = { uri: uri.toString() };
        let cursor = { textDocument: doc, position: position };
        const req = new RequestType<GoalRequest, Goal[], void>("proof/goals");
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
