import { NotificationType, NotificationType1, VersionedTextDocumentIdentifier, Range } from "vscode-languageclient";

enum CoqFileProgressKind {
    Processing = 1,
    FatalError = 2
}

interface CoqFileProgressProcessingInfo {
    /** Range for which the processing info was reported. */
    range: Range;
    /** Kind of progress that was reported. */
    kind?: CoqFileProgressKind;
}

export interface CoqFileProgressParams {
    /** The text document to which this progress notification applies. */
    textDocument: VersionedTextDocumentIdentifier;

    /**
     * Array containing the parts of the file which are still being processed.
     * The array should be empty if and only if the server is finished processing.
     */
    processing: CoqFileProgressProcessingInfo[];
}

export const coqFileProgress = new NotificationType<CoqFileProgressParams>('$/coq/fileProgress');
