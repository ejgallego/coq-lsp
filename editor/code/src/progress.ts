import { throttle } from "throttle-debounce";
import { Disposable, Range, window, OverviewRulerLane } from "vscode";
import {
  NotificationType,
  VersionedTextDocumentIdentifier,
} from "vscode-languageclient";
import { BaseLanguageClient } from "vscode-languageclient";

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

// Create decoration for fileProgress
const progressDecoration = window.createTextEditorDecorationType({
  overviewRulerColor: "rgba(255,165,0,0.5)",
  overviewRulerLane: OverviewRulerLane.Left,
});

export class FileProgressManager {
  private fileProgress: Disposable;

  constructor(client: BaseLanguageClient) {
    this.fileProgress = client.onNotification(coqFileProgress, (params) => {
      let ranges = params.processing
        .map((fp) => client.protocol2CodeConverter.asRange(fp.range))
        .filter((r) => !r.isEmpty);
      this.updateDecos(params.textDocument.uri, ranges);
    });
  }
  dispose() {
    this.fileProgress.dispose();
    // Wait to clean due to throttle in updateDecos
    setTimeout(this.cleanDecos, 250);
  }
  private updateDecos = throttle(200, (uri: string, ranges: Range[]) => {
    for (const editor of window.visibleTextEditors) {
      if (editor.document.uri.toString() == uri) {
        editor.setDecorations(progressDecoration, ranges);
      }
    }
  });
  private cleanDecos() {
    for (const editor of window.visibleTextEditors) {
      if (
        editor.document.languageId === "coq" ||
        editor.document.languageId === "markdown"
      ) {
        editor.setDecorations(progressDecoration, []);
      }
    }
  }
}
