import { window, commands, ExtensionContext, workspace, WebviewPanel, ViewColumn, Uri } from "vscode";
import { LanguageClient } from "vscode-languageclient/node";
import { GoalPanel } from "./goals";

let client : LanguageClient;
let goalPanel : GoalPanel;

export function activate (context : ExtensionContext) : void {
    window.showInformationMessage('Going to activate!');

    function coqCommand(command : string, fn : () => void) {
        let disposable = commands.registerCommand('coq-lsp.'+command, fn);
        context.subscriptions.push(disposable);
    }
    const restart = () => {
        if (client) {
            client.stop();
        }

        window.showInformationMessage('Going to start!');
 
        const config = workspace.getConfiguration('coq-lsp');
        const initializationOptions = {
            eager_diagnostics: config.eager_diagnostics,
            ok_diagnostics: config.ok_diagnostics
        };

        const clientOptions = {
            documentSelector: [
                {scheme: 'file', language: 'coq'}
            ],
            initializationOptions
        };
        const serverOptions = { command: config.path, args: config.args };

        client = new LanguageClient(
            'coq-lsp-server',
            'Coq Language Server',
            serverOptions,
            clientOptions
        );
        client.start();

        // XXX: Fix this mess with the lifetime of the panel  
        let panel = window.createWebviewPanel('goals', 'Goals', ViewColumn.Two, {});
        const styleUri = panel.webview.asWebviewUri(Uri.joinPath(context.extensionUri, 'media', 'styles.css'));
        goalPanel = new GoalPanel(client, panel, styleUri);
};

    const checkPanelAlive = () => {
        if(!goalPanel) {
            let panel = window.createWebviewPanel('goals', 'Goals', ViewColumn.Two, {});
            const styleUri = panel.webview.asWebviewUri(Uri.joinPath(context.extensionUri, 'media', 'styles.css'));
            goalPanel = new GoalPanel(client, panel, styleUri);
        }
    }
    const goals = () => {
        checkPanelAlive();
        let uri = window.activeTextEditor?.document?.uri;
        let position = window.activeTextEditor?.selection?.active;
        if(uri && position) {
            goalPanel.update(uri, position);
        }
    }   

    coqCommand('restart', restart);
    coqCommand('goals', goals);

    restart();
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}