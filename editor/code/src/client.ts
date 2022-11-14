import { window, commands, ExtensionContext, workspace } from "vscode";
import { LanguageClient } from "vscode-languageclient/node";

let client : LanguageClient;

export function activate (context : ExtensionContext) : void {
    window.showInformationMessage('Going to activate!');

    const clientOptions = {
        documentSelector: [
            {scheme: 'file', language: 'coq'}
        ]
    };
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
        const serverOptions = { command: config.path, args: config.args };

        client = new LanguageClient(
            'coq-lsp-server',
            'Coq Language Server',
            serverOptions,
            clientOptions
        );
        client.start();
    };

    coqCommand('restart', restart);
    restart();
}

export function deactivate(): Thenable<void> | undefined {
	if (!client) {
		return undefined;
	}
	return client.stop();
}