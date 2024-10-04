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
  languages,
  Uri,
  TextEditorVisibleRangesChangeEvent,
  InputBoxOptions,
} from "vscode";

import * as vscode from "vscode";
import * as lsp from "vscode-languageserver-types";

import {
  BaseLanguageClient,
  DidChangeConfigurationNotification,
  DidChangeConfigurationParams,
  LanguageClientOptions,
  NotificationType,
  RequestType,
  RevealOutputChannelOn,
  VersionedTextDocumentIdentifier,
} from "vscode-languageclient";
import {
  FlecheDocumentParams,
  FlecheDocument,
  FlecheSaveParams,
  GoalRequest,
  GoalAnswer,
  PpString,
  DocumentPerfParams,
  ViewRangeParams,
} from "../lib/types";

import {
  CoqLanguageStatus,
  defaultVersion,
  defaultStatus,
  coqServerVersion,
  coqServerStatus,
} from "./status";
import { CoqLspClientConfig, CoqLspServerConfig, CoqSelector } from "./config";
import { InfoPanel, goalReq } from "./goals";
import { FileProgressManager } from "./progress";
import { coqPerfData, PerfDataView } from "./perf";
import { sentenceNext, sentencePrevious } from "./edit";
import { HeatMap, HeatMapConfig } from "./heatmap";
import { petanqueStart, petanqueRun, petSetClient } from "./petanque";
import { debounce, throttle } from "throttle-debounce";

// Convert perf data to VSCode format
function toVsCodePerf(
  p: DocumentPerfParams<lsp.Range>
): DocumentPerfParams<vscode.Range> {
  let textDocument = p.textDocument;
  let summary = p.summary;
  let timings = p.timings.map((t) => {
    return {
      range: client.protocol2CodeConverter.asRange(t.range),
      info: t.info,
    };
  });
  return { textDocument, summary, timings };
}

let config: CoqLspClientConfig;
let serverConfig: CoqLspServerConfig;

let client: BaseLanguageClient;

// Lifetime of the info panel == extension lifetime.
let infoPanel: InfoPanel;

// Lifetime of the fileProgress setup == client lifetime
let fileProgress: FileProgressManager;

// Status Bar Button
let lspStatusItem: StatusBarItem;

// Language Status Indicators
let languageStatus: CoqLanguageStatus;
let languageVersionHook: Disposable;
let languageStatusHook: Disposable;

// Lifetime of the perf data setup == client lifetime for the hook, extension for the webview
let perfDataView: PerfDataView;
let perfDataHook: Disposable;

let heatMap: HeatMap;

// Client Factory types
export type ClientFactoryType = (
  context: ExtensionContext,
  clientOptions: LanguageClientOptions,
  wsConfig: WorkspaceConfiguration
) => BaseLanguageClient;

// Extension API type (note this doesn't live in `lib` as this is VSCode specific)
export interface CoqLspAPI {
  /**
   * Query goals from Coq
   */
  goalsRequest(params: GoalRequest): Promise<GoalAnswer<PpString>>;

  /**
   * Register callback on user-initiated goals request
   */
  onUserGoals(fn: (goals: GoalAnswer<String>) => void): Disposable;
}

export function activateCoqLSP(
  context: ExtensionContext,
  clientFactory: ClientFactoryType
): CoqLspAPI {
  window.showInformationMessage("Coq LSP Extension: Going to activate!");

  // Update config on client and server
  function configDidChange(wsConfig: any): CoqLspServerConfig {
    config = CoqLspClientConfig.create(wsConfig);
    let client_version = context.extension.packageJSON.version;
    let settings = CoqLspServerConfig.create(client_version, wsConfig);
    let params: DidChangeConfigurationParams = { settings };

    if (client && client.isRunning()) {
      let type = DidChangeConfigurationNotification.type;
      client.sendNotification(type, params);
    }

    // Store setting on the server for local use
    serverConfig = settings;
    return settings;
  }

  function coqCommand(
    command: string,
    fn: (...args: any[]) => void | Promise<void>
  ) {
    let disposable = commands.registerCommand("coq-lsp." + command, fn);
    context.subscriptions.push(disposable);
  }
  function coqEditorCommand(command: string, fn: (editor: TextEditor) => void) {
    // EJGA: we should check for document selector here.
    let disposable = commands.registerTextEditorCommand(
      "coq-lsp." + command,
      fn
    );
    context.subscriptions.push(disposable);
  }

  function checkForVSCoq() {
    let vscoq =
      extensions.getExtension("maximedenes.vscoq") ||
      extensions.getExtension("coq-community.vscoq1");
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
      return client
        .dispose(2000)
        .finally(updateStatusBar)
        .finally(() => {
          infoPanel.dispose();
          fileProgress.dispose();
          perfDataHook.dispose();
          heatMap.dispose();
          languageVersionHook.dispose();
          languageStatusHook.dispose();
        });
    } else return Promise.resolve();
  };

  const start = () => {
    if (client && client.isRunning()) return;

    const wsConfig = workspace.getConfiguration("coq-lsp");

    // This also sets `config` variable
    const initializationOptions: CoqLspServerConfig = configDidChange(wsConfig);

    const clientOptions: LanguageClientOptions = {
      documentSelector: CoqSelector.owned,
      outputChannelName: "Coq LSP Server Events",
      revealOutputChannelOn: RevealOutputChannelOn.Info,
      initializationOptions,
      markdown: { isTrusted: true, supportHtml: true },
    };

    let cP = new Promise<BaseLanguageClient>((resolve) => {
      client = clientFactory(context, clientOptions, wsConfig);
      petSetClient(client);
      fileProgress = new FileProgressManager(client);
      perfDataHook = client.onNotification(coqPerfData, (data) => {
        perfDataView.update(data);
        heatMap.update(toVsCodePerf(data));
      });

      languageVersionHook = client.onNotification(coqServerVersion, (data) => {
        languageStatus.updateVersion(data);
      });

      languageStatusHook = client.onNotification(coqServerStatus, (data) => {
        languageStatus.updateStatus(data, serverConfig.check_only_on_request);
      });

      resolve(client);
    });

    return cP
      .then((client) =>
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
      )
      .catch((error) => {
        let emsg = error.toString();
        console.log(`Error in coq-lsp start: ${emsg}`);
        setFailedStatusBar(emsg);
      });
  };

  const restart = async () => {
    await stop().finally(start);
  };

  const toggle_lazy_checking = async () => {
    let wsConfig = workspace.getConfiguration();
    let newValue = !wsConfig.get<boolean>("coq-lsp.check_only_on_request");
    await wsConfig.update("coq-lsp.check_only_on_request", newValue);
    languageStatus.updateStatus({ status: "Idle", mem: "" }, newValue);
  };

  // switches between the different status of the server
  const toggle = async () => {
    if (client && client.isRunning() && !serverConfig.check_only_on_request) {
      // Server on, and in continous mode, set lazy
      await toggle_lazy_checking().then(updateStatusBar);
    } else if (client && client.isRunning()) {
      // Server on, and in lazy mode, stop
      await stop();
    } else {
      // Server is off, set continous mode and start
      await toggle_lazy_checking().then(start);
    }
  };

  // Start of extension activation:

  // Check VSCoq is not installed
  checkForVSCoq();

  // Config change events setup
  let onDidChange = workspace.onDidChangeConfiguration((cfgChange) => {
    if (cfgChange.affectsConfiguration("coq-lsp")) {
      // Refactor to remove the duplicate call below
      const wsConfig = workspace.getConfiguration("coq-lsp");
      configDidChange(wsConfig);
    }
  });

  context.subscriptions.push(onDidChange);

  // InfoPanel setup.
  infoPanel = new InfoPanel(context.extensionUri);
  context.subscriptions.push(infoPanel);

  const goals = (editor: TextEditor) => {
    if (!client.isRunning()) return;
    let uri = editor.document.uri.toString();
    let version = editor.document.version;

    // XXX: EJGA: For some reason TS doesn't catch the typing error here,
    // beware, because this creates many problems once out of the standard
    // Node-base Language client and object are serialized!
    let cursor = editor.selection.active;
    let position = client.code2ProtocolConverter.asPosition(cursor);
    infoPanel.updateFromServer(
      client,
      uri,
      version,
      position,
      config.pp_format
    );
  };

  const goalsCall = (
    textEditor: TextEditor,
    callKind: TextEditorSelectionChangeKind | undefined
  ) => {
    // Don't trigger the goals if the buffer is not a local Coq buffer
    if (languages.match(CoqSelector.vsls, textEditor.document) > 0) {
      // handle VSLS
      let uri = textEditor.document.uri.toString();
      let version = textEditor.document.version;
      let position = textEditor.selection.active;
      let textDocument = { uri, version };
      infoPanel.notifyLackOfVSLS(textDocument, position);
      return;
    } else if (languages.match(CoqSelector.owned, textEditor.document) < 1)
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

  const viewRangeNotification = new NotificationType<ViewRangeParams>(
    "coq/viewRange"
  );

  let viewRangeHook = window.onDidChangeTextEditorVisibleRanges(
    throttle(400, (evt: TextEditorVisibleRangesChangeEvent) => {
      if (
        config.check_on_scroll &&
        serverConfig.check_only_on_request &&
        languages.match(CoqSelector.owned, evt.textEditor.document) > 0 &&
        evt.visibleRanges[0]
      ) {
        let uri = evt.textEditor.document.uri.toString();
        let version = evt.textEditor.document.version;
        let textDocument = { uri, version };
        let range = client.code2ProtocolConverter.asRange(evt.visibleRanges[0]);
        let params: ViewRangeParams = { textDocument, range };
        client.sendNotification(viewRangeNotification, params);
      }
    })
  );

  context.subscriptions.push(viewRangeHook);

  // Heatmap setup
  heatMap = new HeatMap(
    workspace.getConfiguration("coq-lsp").get("heatmap") as HeatMapConfig
  );

  const heatMapToggle = () => {
    heatMap.toggle();
  };

  // Document request setup
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
    client.sendRequest(docReq, params).then((fd) => {
      // EJGA: uri_result could be used to set the suggested save path
      // for the new editor, however we need to see how to do that
      // and set `content` too for the new editor.
      let path = `${uri.fsPath}-${version}.json`;
      let uri_result = Uri.file(path).with({ scheme: "untitled" });

      let open_options = {
        language: "json",
        content: JSON.stringify(fd, null, 2),
      };
      workspace.openTextDocument(open_options).then((document) => {
        window.showTextDocument(document);
      });
    });
  };

  // Trim notification setup
  const trimNot = new NotificationType<{}>("coq/trimCaches");

  const cacheTrim = () => {
    client.sendNotification(trimNot, {});
  };

  // Save request setup
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
    lspStatusItem.text = "coq-lsp (not active)";
    lspStatusItem.show();
    context.subscriptions.push(lspStatusItem);
  };

  // This stuff should likely go in the CoqLSP client class
  languageStatus = new CoqLanguageStatus(defaultVersion, defaultStatus, false);

  // Ali notes about the status item text: we should keep it short
  // We violate this on the error case, but only because it is exceptional.
  const updateStatusBar = () => {
    if (client && client.isRunning()) {
      if (serverConfig.check_only_on_request) {
        lspStatusItem.text = "$(check) coq-lsp (on-demand checking)";
        lspStatusItem.backgroundColor = undefined;
        lspStatusItem.tooltip = "coq-lsp is running. Click to disable.";
      } else {
        lspStatusItem.text = "$(check) coq-lsp (continous checking)";
        lspStatusItem.backgroundColor = undefined;
        lspStatusItem.tooltip = "coq-lsp is running. Click to disable.";
      }
    } else {
      lspStatusItem.text = "$(circle-slash) coq-lsp (stopped)";
      lspStatusItem.backgroundColor = new ThemeColor(
        "statusBarItem.warningBackground"
      );
      lspStatusItem.tooltip = "coq-lsp has been disabled. Click to enable.";
    }
  };

  const setFailedStatusBar = (emsg: string) => {
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
  coqCommand("trim", cacheTrim);

  coqCommand("toggle_mode", toggle_lazy_checking);

  coqEditorCommand("goals", goals);
  coqEditorCommand("document", getDocument);
  coqEditorCommand("save", saveDocument);

  coqEditorCommand("sentenceNext", sentenceNext);
  coqEditorCommand("sentencePrevious", sentencePrevious);

  coqEditorCommand("heatmap.toggle", heatMapToggle);

  coqEditorCommand("petanque.start", petanqueStart);
  coqEditorCommand("petanque.run", petanqueRun);

  createEnableButton();

  // Fix for bug #750
  const active_editors_for_us = (editors: readonly TextEditor[]) =>
    editors.some(
      (editor) => languages.match(CoqSelector.all, editor.document) > 0
    );

  // We track when new buffers appear, and start the client if so. We
  // dispose of the hook too.
  if (active_editors_for_us(window.visibleTextEditors)) {
    start();
  } else {
    window.onDidChangeVisibleTextEditors((editors) => {
      if (!client || !client.isRunning()) {
        if (active_editors_for_us(editors)) start();
      }
    }, context.subscriptions);
  }

  return {
    goalsRequest: (params) => {
      return client.sendRequest(goalReq, params);
    },
    onUserGoals: (fn) => {
      infoPanel.registerObserver(fn);
      return new Disposable(() => infoPanel.unregisterObserver(fn));
    },
  };
}

export function deactivateCoqLSP(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
