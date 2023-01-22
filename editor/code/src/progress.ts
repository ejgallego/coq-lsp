import { throttle } from "throttle-debounce";
import { Disposable, Range, window, TextEditorDecorationType } from "vscode";
import {
  NotificationType,
  VersionedTextDocumentIdentifier,
} from "vscode-languageclient";
import { LanguageClient } from "vscode-languageclient/node";

enum CoqFileProgressKind {
  Processing = 1,
  FatalError = 2,
}

interface CoqFileProgressProcessingInfo {
  /** Range for which the processing info was reported. */
  range: Range;
  /** Kind of progress that was reported. */
  kind?: CoqFileProgressKind;
}

interface CoqFileProgressParams {
  /** The text document to which this progress notification applies. */
  textDocument: VersionedTextDocumentIdentifier;

  /**
   * Array containing the parts of the file which are still being processed.
   * The array should be empty if and only if the server is finished processing.
   */
  processing: CoqFileProgressProcessingInfo[];
}

const coqFileProgress = new NotificationType<CoqFileProgressParams>(
  "$/coq/fileProgress"
);

export class FileProgressManager {
  private fileProgress: Disposable;
  private decoration: TextEditorDecorationType;

  constructor(client: LanguageClient, decoration: TextEditorDecorationType) {
    this.fileProgress = client.onNotification(coqFileProgress, (params) => {
      let ranges = params.processing
        .map((fp) => client.protocol2CodeConverter.asRange(fp.range))
        .filter((r) => !r.isEmpty);
      this.updateDecos(params.textDocument.uri, ranges);
    });
    this.decoration = decoration;
  }
  dispose() {
    this.fileProgress.dispose();
    this.cleanDecos();
  }
  private updateDecos = throttle(200, (uri: string, ranges: Range[]) => {
    for (const editor of window.visibleTextEditors) {
      if (editor.document.uri.toString() == uri) {
        editor.setDecorations(this.decoration, ranges);
      }
    }
  });
  private cleanDecos() {
    for (const editor of window.visibleTextEditors) {
      if (editor.document.languageId === "coq") {
        editor.setDecorations(this.decoration, []);
      }
    }
  }
}
