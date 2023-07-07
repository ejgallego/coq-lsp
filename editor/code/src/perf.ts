import {
  Disposable,
  Uri,
  WebviewView,
  WebviewViewProvider,
  WebviewViewResolveContext,
  window,
} from "vscode";
import { NotificationType } from "vscode-languageclient";
import { DocumentPerfParams } from "../lib/types";

export const coqPerfData = new NotificationType<DocumentPerfParams>(
  "$/coq/filePerfData",
);

export class PerfDataView implements Disposable {
  private panel: Disposable;
  private updateWebView: (data: DocumentPerfParams) => void = () => {};

  constructor(extensionUri: Uri) {
    let resolveWebviewView = (
      webview: WebviewView,
      context: WebviewViewResolveContext<any>,
    ) => {
      webview.webview.options = {
        // Allow scripts in the webview
        enableScripts: true,
      };

      const styleUri = webview.webview.asWebviewUri(
        Uri.joinPath(extensionUri, "out", "views", "perf", "index.css"),
      );

      const scriptUri = webview.webview.asWebviewUri(
        Uri.joinPath(extensionUri, "out", "views", "perf", "index.js"),
      );

      webview.webview.html = ` <!DOCTYPE html>
      <html lang="en">
      <head>
          <meta charset="UTF-8">
          <link rel="stylesheet" type="text/css" href="${styleUri}">
          <meta name="viewport" content="width=device-width, initial-scale=1.0">
          <script src="${scriptUri}" type="module"></script>
          <title>Coq's info panel</title>
      </head>
      <body>
      <div id="root">
      </div>
      </body>
      </html>`;

      this.updateWebView = (params: DocumentPerfParams) => {
        webview.webview.postMessage({ method: "update", params });
      };
    };
    let perfProvider: WebviewViewProvider = { resolveWebviewView };
    this.panel = window.registerWebviewViewProvider(
      "coqPerfView",
      perfProvider,
    );
  }
  dispose() {
    this.panel.dispose();
  }
  update(data: DocumentPerfParams) {
    this.updateWebView(data);
  }
}
