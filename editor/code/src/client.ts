import { throttle } from "throttle-debounce";
import {
    window,
    commands,
    ExtensionContext,
    workspace,
    ViewColumn,
    Uri,
    TextEditor,
    OverviewRulerLane
} from "vscode";
import * as vscode from "vscode";
import { Range } from "vscode-languageclient";
import { 
    LanguageClient,
    LanguageClientOptions,
    RevealOutputChannelOn,
} from "vscode-languageclient/node";
import { GoalPanel } from "./goals";
import { coqFileProgress, CoqFileProgressParams } from "./progress";

let client: LanguageClient;
let goalPanel: GoalPanel | null;

export function panelFactory(context: ExtensionContext) {
    let panel = window.createWebviewPanel("goals", "Goals", ViewColumn.Two, {});
    panel.onDidDispose(() => {
        goalPanel = null;
    });
    const styleUri = panel.webview.asWebviewUri(
        Uri.joinPath(context.extensionUri, "media", "styles.css")
    );
    return new GoalPanel(client, panel, styleUri);
}

export function activate(context: ExtensionContext): void {
    window.showInformationMessage("Going to activate!");

    function coqCommand(command: string, fn: () => void) {
        let disposable = commands.registerCommand("coq-lsp." + command, fn);
        context.subscriptions.push(disposable);
    }
    function coqEditorCommand(command: string, fn: (editor: TextEditor) => void) {
        let disposable = commands.registerTextEditorCommand("coq-lsp." + command, fn);
        context.subscriptions.push(disposable);
    }
    const restart = () => {
        if (client) {
            client.stop();
            if (goalPanel) goalPanel.dispose();
        }

        window.showInformationMessage("Coq Language Server: starting");

        const config = workspace.getConfiguration("coq-lsp");
        const initializationOptions = {
            eager_diagnostics: config.eager_diagnostics,
            ok_diagnostics: config.ok_diagnostics,
        };

        const clientOptions: LanguageClientOptions = {
            documentSelector: [{ scheme: "file", language: "coq" }],
            outputChannelName: "Coq LSP Server Events",
            revealOutputChannelOn: RevealOutputChannelOn.Info,
            initializationOptions,
        };
        const serverOptions = { command: config.path, args: config.args };

        client = new LanguageClient(
            "coq-lsp-server",
            "Coq Language Server",
            serverOptions,
            clientOptions
        );
        client.start();

        client.onNotification(coqFileProgress, (params) => {
            let ranges = params.processing.map((fp) => rangeProto2Code(fp.range))
                                          .filter((r) => ! r.isEmpty);
            updateDecos(params.textDocument.uri, ranges);
        });

        // XXX: Fix this mess with the lifetime of the panel
        goalPanel = panelFactory(context);
    };
    const progressDecoration = window.createTextEditorDecorationType(
        { overviewRulerColor: 'rgba(255,165,0,0.5)', overviewRulerLane: OverviewRulerLane.Left}
    );

    const updateDecos = throttle(200,
        function(uri : string, ranges : vscode.Range[]) {
            for (const editor of window.visibleTextEditors) {
                if (editor.document.uri.toString() == uri) {
                    editor.setDecorations(progressDecoration, ranges);
                }
            }
        });

    const rangeProto2Code = function(r : Range) {
        return new vscode.Range(r.start.line, r.start.character, r.end.line, r.end.character);
    };
    const checkPanelAlive = () => {
        if (!goalPanel) {
            goalPanel = panelFactory(context);
        }
    };

    const goals = (editor : TextEditor) => {
        checkPanelAlive();
        let uri = editor.document.uri;
        let position = editor.selection.active;
        if (goalPanel) {
            goalPanel.update(uri, position);
        }
    };

    coqCommand("restart", restart);
    coqEditorCommand("goals", goals);

    restart();
}

export function deactivate(): Thenable<void> | undefined {
    if (!client) {
        return undefined;
    }
    return client.stop();
}
