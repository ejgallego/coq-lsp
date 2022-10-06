'use strict';

const vscode = require("vscode");
const vscc = require("vscode-languageclient");

function activate(context) {
    vscode.window.showInformationMessage('Starting coq-lsp!');
    let clientOptions = {
        documentSelector: [
            { scheme: 'file', language: 'coq' }
        ]
    };

    let client = null;

    const start = () => {
        if (client) {
            client.stop();
        }
        client = new vscc.LanguageClient(
            'coq-lsp-server',
            'Coq Language Server',
            {
                command: 'coq-lsp',
                args: ['--std']
            },
            clientOptions
        );
        context.subscriptions.push(client.start());
    };


    const restart = () => {
        vscode.window.showInformationMessage('Restarting coq-lsp!');
        start();
    };

    vscode.commands.registerCommand('vsc-galinas.restart', restart);
    start();
}

exports.activate = activate;
