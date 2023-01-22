import {
  window,
  commands,
  extensions,
  ExtensionContext,
  workspace,
  TextEditor,
  OverviewRulerLane,
  TextEditorSelectionChangeEvent,
  TextEditorSelectionChangeKind,
} from "vscode";
import {
  LanguageClient,
  ServerOptions,
  LanguageClientOptions,
  RevealOutputChannelOn,
} from "vscode-languageclient/node";

import { CoqLspClientConfig, CoqLspServerConfig } from "./config";
import { InfoPanel } from "./goals";
import { FileProgressManager } from "./progress";

let config: CoqLspClientConfig;
let client: LanguageClient;
// Lifetime of the info panel == extension lifetime.
let infoPanel: InfoPanel;
// Lifetime of the fileProgress setup == client lifetime
let fileProgress: FileProgressManager;

export function activate(context: ExtensionContext): void {
  window.showInformationMessage("Coq LSP Extension: Going to activate!");

  function coqCommand(command: string, fn: () => void) {
    let disposable = commands.registerCommand("coq-lsp." + command, fn);
    context.subscriptions.push(disposable);
  }
  function coqEditorCommand(command: string, fn: (editor: TextEditor) => void) {
    let disposable = commands.registerTextEditorCommand(
      "coq-lsp." + command,
      fn
    );
    context.subscriptions.push(disposable);
  }
  function checkForVSCoq() {
    let vscoq = extensions.getExtension("maximedenes.vscoq");
    if (vscoq?.isActive) {
      window.showErrorMessage(
        "Coq LSP Extension: VSCoq extension has been detected, you need to deactivate it for coq-lsp to work properly.",
        { modal: false, detail: "thanks for your understanding" },
        { title: "Understood" }
      );
    }
  }

  const restart = () => {
    if (client) {
      client.stop();
      infoPanel.dispose();
      fileProgress.dispose();
    }

    const wsConfig = workspace.getConfiguration("coq-lsp");
    config = CoqLspClientConfig.create(wsConfig);

    let client_version = context.extension.packageJSON.version;
    const initializationOptions = CoqLspServerConfig.create(
      client_version,
      wsConfig
    );

    const clientOptions: LanguageClientOptions = {
      documentSelector: [{ scheme: "file", language: "coq" }],
      outputChannelName: "Coq LSP Server Events",
      revealOutputChannelOn: RevealOutputChannelOn.Info,
      initializationOptions,
      markdown: { isTrusted: true, supportHtml: true },
    };
    const serverOptions: ServerOptions = {
      command: wsConfig.path,
      args: wsConfig.args,
    };

    client = new LanguageClient(
      "coq-lsp",
      "Coq LSP Server",
      serverOptions,
      clientOptions
    );
    client.start();

    fileProgress = new FileProgressManager(client, progressDecoration);
  };

  // Main extension routine start:

  // Create decoration for fileProgress
  const progressDecoration = window.createTextEditorDecorationType({
    overviewRulerColor: "rgba(255,165,0,0.5)",
    overviewRulerLane: OverviewRulerLane.Left,
  });

  // Check VSCoq is not installed
  checkForVSCoq();

  // InfoPanel setup.
  infoPanel = new InfoPanel(context.extensionUri);
  context.subscriptions.push(infoPanel);

  const goals = (editor: TextEditor) => {
    let uri = editor.document.uri;
    let version = editor.document.version;
    let position = editor.selection.active;
    infoPanel.updateFromServer(client, uri, version, position);
  };

  let goalsHook = window.onDidChangeTextEditorSelection(
    (evt: TextEditorSelectionChangeEvent) => {
      if (evt.textEditor.document.languageId != "coq") return;

      const kind =
        evt.kind == TextEditorSelectionChangeKind.Mouse
          ? 1
          : evt.kind == TextEditorSelectionChangeKind.Keyboard
          ? 2
          : evt.kind
          ? evt.kind
          : 3;
      // When evt.kind is null, it often means it was due to an
      // edit, we want to re-trigger in that case

      const show = kind <= config.show_goals_on;

      if (show) {
        goals(evt.textEditor);
      }
    }
  );

  context.subscriptions.push(goalsHook);

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
