import {
  window,
  commands,
  extensions,
  ExtensionContext,
  workspace,
  TextEditor,
  TextEditorSelectionChangeEvent,
  TextEditorSelectionChangeKind,
  StatusBarAlignment,
  StatusBarItem,
  ThemeColor,
} from "vscode";
import {
  LanguageClient,
  ServerOptions,
  LanguageClientOptions,
  RevealOutputChannelOn,
} from "vscode-languageclient/node";
import {
  RequestType,
  VersionedTextDocumentIdentifier,
} from "vscode-languageclient";
import { FlecheDocumentParams, FlecheDocument } from "../lib/types";
import { CoqLspClientConfig, CoqLspServerConfig } from "./config";
import { InfoPanel } from "./goals";
import { FileProgressManager } from "./progress";

let config: CoqLspClientConfig;
let client: LanguageClient;
// Lifetime of the info panel == extension lifetime.
let infoPanel: InfoPanel;
// Lifetime of the fileProgress setup == client lifetime
let fileProgress: FileProgressManager;
// Status Bar Button
let lspStatusItem: StatusBarItem;

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
  // Hide .vo, .aux files, etc...
  let activationConfig = workspace.getConfiguration();
  let updateIgnores = activationConfig.get("coq-lsp.updateIgnores") ?? true;
  if (updateIgnores) {
    let fexc: any = activationConfig.get("files.exclude");
    activationConfig.update("files.exclude", {
      "**/*.vo": true,
      "**/*.vok": true,
      "**/*.vos": true,
      "**/*.aux": true,
      "**/*.glob": true,
      ...fexc,
    });
  }
  const stop = () => {
    if (client && client.isRunning()) {
      client
        .dispose(2000)
        .then(updateStatusBar)
        .then(() => {
          infoPanel.dispose();
          fileProgress.dispose();
        });
    }
  };

  const start = () => {
    if (client && client.isRunning()) return;

    const wsConfig = workspace.getConfiguration("coq-lsp");
    config = CoqLspClientConfig.create(wsConfig);

    let client_version = context.extension.packageJSON.version;
    const initializationOptions = CoqLspServerConfig.create(
      client_version,
      wsConfig
    );

    const clientOptions: LanguageClientOptions = {
      documentSelector: [
        { scheme: "file", language: "coq" },
        { scheme: "file", language: "coqmarkdown" },
      ],
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

    fileProgress = new FileProgressManager(client);
    client
      .start()
      .then(updateStatusBar)
      .then(() => {
        if (window.activeTextEditor) {
          goalsCall(
            window.activeTextEditor,
            TextEditorSelectionChangeKind.Command
          );
        }
      });
  };

  const restart = () => {
    stop();
    start();
  };

  const toggle = () => {
    if (client && client.isRunning()) {
      stop();
    } else {
      start();
    }
  };

  // Start of extension activation:

  // Check VSCoq is not installed
  checkForVSCoq();

  // InfoPanel setup.
  infoPanel = new InfoPanel(context.extensionUri);
  context.subscriptions.push(infoPanel);

  const goals = (editor: TextEditor) => {
    if (!client.isRunning()) return;
    let uri = editor.document.uri;
    let version = editor.document.version;
    let position = editor.selection.active;
    infoPanel.updateFromServer(client, uri, version, position);
  };

  const goalsCall = (
    textEditor: TextEditor,
    callKind: TextEditorSelectionChangeKind | undefined
  ) => {
    if (
      textEditor.document.languageId != "coq" &&
      textEditor.document.languageId != "coqmarkdown"
    )
      return;

    const kind =
      callKind == TextEditorSelectionChangeKind.Mouse
        ? 1
        : callKind == TextEditorSelectionChangeKind.Keyboard
        ? 2
        : callKind
        ? callKind
        : 3;
    // When evt.kind is null, it often means it was due to an
    // edit, we want to re-trigger in that case

    const show = kind <= config.show_goals_on;

    if (show) {
      goals(textEditor);
    }
  };

  let goalsHook = window.onDidChangeTextEditorSelection(
    (evt: TextEditorSelectionChangeEvent) => {
      goalsCall(evt.textEditor, evt.kind);
    }
  );

  context.subscriptions.push(goalsHook);

  const docReq = new RequestType<FlecheDocumentParams, FlecheDocument, void>(
    "coq/getDocument"
  );

  let getDocument = (editor: TextEditor) => {
    let uri = editor.document.uri;
    let version = editor.document.version;
    let textDocument = VersionedTextDocumentIdentifier.create(
      uri.toString(),
      version
    );
    let params: FlecheDocumentParams = { textDocument };
    client.sendRequest(docReq, params).then((fd) => console.log(fd));
  };
  const createEnableButton = () => {
    lspStatusItem = window.createStatusBarItem(
      "coq-lsp.enable",
      StatusBarAlignment.Left,
      0
    );
    lspStatusItem.command = "coq-lsp.toggle";
    lspStatusItem.text = "coq-lsp";
    lspStatusItem.show();
    context.subscriptions.push(lspStatusItem);
  };

  const updateStatusBar = () => {
    if (client && client.isRunning()) {
      lspStatusItem.text = "$(check) coq-lsp (running)";
      lspStatusItem.backgroundColor = undefined;
      lspStatusItem.tooltip = "coq-lsp is running. Click to disable.";
    } else {
      lspStatusItem.text = "$(circle-slash) coq-lsp (stopped)";
      lspStatusItem.backgroundColor = new ThemeColor(
        "statusBarItem.warningBackground"
      );
      lspStatusItem.tooltip = "coq-lsp has been disabled. Click to enable.";
    }
  };

  coqCommand("stop", stop);
  coqCommand("start", start);
  coqCommand("restart", restart);
  coqCommand("toggle", toggle);

  coqEditorCommand("goals", goals);
  coqEditorCommand("document", getDocument);

  createEnableButton();

  start();
}
export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
