'use strict';

const vscode = require("vscode");
const vscc = require("vscode-languageclient");

function activate (context) {
    vscode.window.showInformationMessage('Going to activate!');
    let clientOptions = {
        documentSelector: [
            {scheme: 'file', language: 'coq'}
        ]
    };

    let client = null;

    const restart = () => {
        if (client) {
            client.stop();
        }
        vscode.window.showInformationMessage('Going to start!');
        client = new vscc.LanguageClient(
            'coq-lsp-server',
            'Coq Language Server',
            {
                command: 'coq-lsp',
                args: [ '--std' ]
            },
            clientOptions
        );
        context.subscriptions.push(client.start());
    };

    vscode.commands.registerCommand('vsc-galinas.restart', restart);

    restart();
}

exports.activate = activate;
