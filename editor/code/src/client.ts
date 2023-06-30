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
  WorkspaceConfiguration,
  Disposable,
} from "vscode";

import {
  BaseLanguageClient,
  LanguageClientOptions,
  RequestType,
  RevealOutputChannelOn,
  VersionedTextDocumentIdentifier,
} from "vscode-languageclient";
import {
  FlecheDocumentParams,
  FlecheDocument,
  FlecheSaveParams,
} from "../lib/types";
import { CoqLspClientConfig, CoqLspServerConfig } from "./config";
import { InfoPanel } from "./goals";
import { FileProgressManager } from "./progress";
import { coqPerfData, PerfDataView } from "./perf";

let config: CoqLspClientConfig;
let client: BaseLanguageClient;

// Lifetime of the info panel == extension lifetime.
let infoPanel: InfoPanel;

// Lifetime of the fileProgress setup == client lifetime
let fileProgress: FileProgressManager;

// Status Bar Button
let lspStatusItem: StatusBarItem;

// Lifetime of the perf data setup == client lifetime for the hook, extension for the webview
let perfDataView: PerfDataView;
let perfDataHook: Disposable;

// Client Factory types
export type ClientFactoryType = (
  context: ExtensionContext,
  clientOptions: LanguageClientOptions,
  wsConfig: WorkspaceConfiguration
) => BaseLanguageClient;

export function activateCoqLSP(
  context: ExtensionContext,
  clientFactory: ClientFactoryType
): void {
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
          perfDataHook.dispose();
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
        { scheme: "file", language: "markdown", pattern: "**/*.mv" },
      ],
      outputChannelName: "Coq LSP Server Events",
      revealOutputChannelOn: RevealOutputChannelOn.Info,
      initializationOptions,
      markdown: { isTrusted: true, supportHtml: true },
    };

    let cP = new Promise<BaseLanguageClient>((resolve) => {
      client = clientFactory(context, clientOptions, wsConfig);
      fileProgress = new FileProgressManager(client);
      perfDataHook = client.onNotification(coqPerfData, (data) => {
        perfDataView.update(data);
      });
      resolve(client);
    });

    cP.then((client) =>
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
        })
    ).catch((error) => {
      let emsg = error.toString();
      console.log(`Error in coq-lsp start: ${emsg}`);
      setFailedStatuBar(emsg);
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
      textEditor.document.languageId != "markdown"
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

  const getDocument = (editor: TextEditor) => {
    let uri = editor.document.uri;
    let version = editor.document.version;
    let textDocument = VersionedTextDocumentIdentifier.create(
      uri.toString(),
      version
    );
    let params: FlecheDocumentParams = { textDocument };
    client.sendRequest(docReq, params).then((fd) => console.log(fd));
  };

  const saveReq = new RequestType<FlecheDocumentParams, void, void>(
    "coq/saveVo"
  );

  const saveDocument = (editor: TextEditor) => {
    let uri = editor.document.uri;
    let version = editor.document.version;
    let textDocument = VersionedTextDocumentIdentifier.create(
      uri.toString(),
      version
    );
    let params: FlecheSaveParams = { textDocument };
    client
      .sendRequest(saveReq, params)
      .then(() => console.log("document saved", uri.toString()))
      .catch((error) => {
        let err_message = error.toString();
        console.log(`error in save: ${err_message}`);
        window.showErrorMessage(err_message);
      });
  };

  const createEnableButton = () => {
    lspStatusItem = window.createStatusBarItem(
      "coq-lsp.enable",
      StatusBarAlignment.Left,
      0
    );
    lspStatusItem.command = "coq-lsp.toggle";
    lspStatusItem.text = "coq-lsp (activating)";
    lspStatusItem.show();
    context.subscriptions.push(lspStatusItem);
  };

  // Ali notes about the status item text: we should keep it short
  // We violate this on the error case, but only because it is exceptional.
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

  const setFailedStatuBar = (emsg: string) => {
    lspStatusItem.text = "$(circle-slash) coq-lsp (failed to start)";
    lspStatusItem.backgroundColor = new ThemeColor(
      "statusBarItem.errorBackground"
    );
    lspStatusItem.tooltip = `coq-lsp couldn't start: ${emsg} Click to retry.`;
  };

  perfDataView = new PerfDataView(context.extensionUri);
  context.subscriptions.push(perfDataView);

  coqCommand("stop", stop);
  coqCommand("start", start);

  coqCommand("restart", restart);
  coqCommand("toggle", toggle);

  coqEditorCommand("goals", goals);
  coqEditorCommand("document", getDocument);
  coqEditorCommand("save", saveDocument);

  createEnableButton();

  start();
}
export function deactivateCoqLSP(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
