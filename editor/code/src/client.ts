import { throttle } from "throttle-debounce";
import {
  window,
  commands,
  ExtensionContext,
  workspace,
  ViewColumn,
  Uri,
  TextEditor,
  OverviewRulerLane,
  WorkspaceConfiguration,
} from "vscode";
import * as vscode from "vscode";
import { Range } from "vscode-languageclient";
import {
  LanguageClient,
  ServerOptions,
  LanguageClientOptions,
  RevealOutputChannelOn,
} from "vscode-languageclient/node";
import { GoalPanel } from "./goals";
import { coqFileProgress } from "./progress";

enum ShowGoalsOnCursorChange {
  Never = 0,
  OnMouse = 1,
  OnMouseAndKeyboard = 2,
  OnMouseKeyboardCommand = 3,
}

interface CoqLspServerConfig {
  client_version: string;
  eager_diagnostics: boolean;
  ok_diagnostics: boolean;
  goal_after_tactic: boolean;
  show_coq_info_messages: boolean;
  show_notices_as_diagnostics: boolean;
  admit_on_bad_qed: boolean;
}

interface CoqLspClientConfig {
  show_goals_on: ShowGoalsOnCursorChange;
}

let config: CoqLspClientConfig;
let client: LanguageClient;
let goalPanel: GoalPanel | null;
let fileProgress: vscode.Disposable | null;

export function panelFactory(context: ExtensionContext) {
  let webviewOpts: vscode.WebviewOptions = { enableScripts: true };
  let panel = window.createWebviewPanel(
    "goals",
    "Goals",
    ViewColumn.Two,
    webviewOpts
  );
  panel.onDidDispose(() => {
    goalPanel = null;
  });
  const styleUri = panel.webview.asWebviewUri(
    Uri.joinPath(context.extensionUri, "out", "view", "index.css")
  );
  const scriptUri = panel.webview.asWebviewUri(
    Uri.joinPath(context.extensionUri, "out", "view", "index.js")
  );
  return new GoalPanel(client, panel, styleUri, scriptUri);
}

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
  const restart = () => {
    if (client) {
      client.stop();
      if (goalPanel) goalPanel.dispose();
      if (fileProgress) {
        fileProgress.dispose();
        cleanDecos();
      }
    }

    // EJGA: didn't find a way to make CoqLspConfig a subclass of WorkspaceConfiguration
    // despite that class being open. Would be nice to avoid this copy indeed.
    const wsConfig = workspace.getConfiguration("coq-lsp");
    config = { show_goals_on: wsConfig.show_goals_on };
    const initializationOptions: CoqLspServerConfig = {
      client_version: context.extension.packageJSON.version,
      eager_diagnostics: wsConfig.eager_diagnostics,
      ok_diagnostics: wsConfig.ok_diagnostics,
      goal_after_tactic: wsConfig.goal_after_tactic,
      show_coq_info_messages: wsConfig.show_coq_info_messages,
      show_notices_as_diagnostics: wsConfig.show_notices_as_diagnostics,
      admit_on_bad_qed: wsConfig.admit_on_bad_qed,
    };

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

    fileProgress = client.onNotification(coqFileProgress, (params) => {
      let ranges = params.processing
        .map((fp) => rangeProto2Code(fp.range))
        .filter((r) => !r.isEmpty);
      updateDecos(params.textDocument.uri, ranges);
    });

    // XXX: Fix this mess with the lifetime of the panel
    goalPanel = panelFactory(context);
  };

  const progressDecoration = window.createTextEditorDecorationType({
    overviewRulerColor: "rgba(255,165,0,0.5)",
    overviewRulerLane: OverviewRulerLane.Left,
  });

  const updateDecos = throttle(
    200,
    function (uri: string, ranges: vscode.Range[]) {
      for (const editor of window.visibleTextEditors) {
        if (editor.document.uri.toString() == uri) {
          editor.setDecorations(progressDecoration, ranges);
        }
      }
    }
  );

  const cleanDecos = function () {
    for (const editor of window.visibleTextEditors) {
      if (editor.document.languageId === "coq") {
        editor.setDecorations(progressDecoration, []);
      }
    }
  };

  const rangeProto2Code = function (r: Range) {
    return new vscode.Range(
      r.start.line,
      r.start.character,
      r.end.line,
      r.end.character
    );
  };
  const checkPanelAlive = () => {
    if (!goalPanel) {
      goalPanel = panelFactory(context);
    }
  };

  const goals = (editor: TextEditor) => {
    checkPanelAlive();
    let uri = editor.document.uri;
    let version = editor.document.version;
    let position = editor.selection.active;
    if (goalPanel) {
      goalPanel.update(uri, version, position);
    }
  };

  let disposable = window.onDidChangeTextEditorSelection(
    (evt: vscode.TextEditorSelectionChangeEvent) => {
      if (evt.textEditor.document.languageId != "coq") return;

      const kind =
        evt.kind == vscode.TextEditorSelectionChangeKind.Mouse
          ? 1
          : evt.kind == vscode.TextEditorSelectionChangeKind.Keyboard
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

  context.subscriptions.push(disposable);

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
