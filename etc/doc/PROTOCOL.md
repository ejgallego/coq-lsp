# coq-lsp protocol documentation

## Introduction and preliminaries

`coq-lsp` should be usable by standard LSP clients, however it
implements some extensions tailored to improve Coq-specific use.

As of today, this document is written for the 3.17 version of the LSP specification:
https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification

See also the upstream LSP issue on generic support for Proof
Assistants
https://github.com/microsoft/language-server-protocol/issues/1414

## Language server protocol support table

If a feature doesn't appear here it usually means it is not planned in the short term:

| Method                            | Support | Notes                                                      |
|-----------------------------------|---------|------------------------------------------------------------|
| `initialize`                      | Partial | We don't obey the advertised client capabilities           |
| `client/registerCapability`       | No      | Not planned ATM                                            |
| `$/setTrace`                      | Yes      |                                                    |
| `$/logTrace`                      | Yes      |                                                            |
| `window/logMessage`               | Yes     |                                                            |
|-----------------------------------|---------|------------------------------------------------------------|
| `textDocument/didOpen`            | Yes     | We can't reuse Memo tables yet                             |
| `textDocument/didChange`          | Yes     | We only support `TextDocumentSyncKind.Full` for now        |
| `textDocument/didClose`           | Partial | We'd likely want to save a `.vo` file on close if possible |
| `textDocument/didSave`            | No      |                                                            |
|-----------------------------------|---------|------------------------------------------------------------|
| `notebookDocument/didOpen`        | No      | Planned                                                    |
|-----------------------------------|---------|------------------------------------------------------------|
| `textDocument/declaration`        | No      | Planned, blocked on upstream issues                        |
| `textDocument/definition`         | No      | Planned, blocked on upstream issues (#53)                  |
| `textDocument/references`         | No      | Planned, blocked on upstream issues                        |
| `textDocument/hover`              | Yes     |                                                            |
| `textDocument/codeLens`           | No      |                                                            |
| `textDocument/foldingRange`       | No      |                                                            |
| `textDocument/documentSymbol`     | Yes     | Needs more work as to provide better results               |
| `textDocument/semanticTokens`     | No      | Planned                                                    |
| `textDocument/inlineValue`        | No      | Planned                                                    |
| `textDocument/inlayHint`          | No      | Planned                                                    |
| `textDocument/completion`         | Partial | Needs more work locally and upstream (#50)                 |
| `textDocument/publishDiagnostics` | Yes     |                                                            |
| `textDocument/diagnostic`         | No      | Planned, issue #49                                         |
| `textDocument/codeAction`         | No      | Planned                                                    |
|-----------------------------------|---------|------------------------------------------------------------|
| `workspace/workspaceFolders`      | No      |                                                            |
|-----------------------------------|---------|------------------------------------------------------------|


## Extensions to the LSP specification

As of today, `coq-lsp` implements two extensions to the LSP spec. Note
that none of them are stable yet:

### Goal Display

In order to display proof goals, `coq-lsp` supports the `proof/goals` request, parameters are:
```typescript
interface GoalRequest {
    textDocument: TextDocumentIdentifier;
    position: Position;
}
```

Answer to the request is a `Goal[]` object, where
```typescript
interface Hyp {
    names: string;
    ty: string;
}

interface Goal {
    ty: string;
    hyps: Hyp[];
}

interface GoalAnswer {
    textDocument: VersionedTextDocumentIdentifier;
    position: Position;
    goals : Goal[];
}

```

which can be then rendered by the client in way that is desired.

`proof/goals` was first used in the lambdapi-lsp server implementation, and we adapted it to `coq-lsp`.

#### Changelog

- v2: include position and document in the request response
- v1: initial version, imported from lambdapi-lsp

### File checking progress

The `$/coq/fileProgress` notification is sent from server to client to
describe the ranges of the document that have been processed.

It is modelled after `$/lean/fileProgress`, see
https://github.com/microsoft/language-server-protocol/issues/1414 for more information.

```typescript
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

interface CoqFileProgressParams {
    /** The text document to which this progress notification applies. */
    textDocument: VersionedTextDocumentIdentifier;

    /**
     * Array containing the parts of the file which are still being processed.
     * The array should be empty if and only if the server is finished processing.
     */
    processing: CoqFileProgressProcessingInfo[];
}
```

#### Changelog

- v1: exact copy from Lean protocol (spec under Apache License)
