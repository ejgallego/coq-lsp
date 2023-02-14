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
| `$/setTrace`                      | Yes     |                                                            |
| `$/logTrace`                      | Yes     |                                                            |
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


### URIs accepted by coq-lsp

`coq-lsp` only accepts `file:///` URIs; moreover, the URIs sent to the
server must be able to be mapped back to a Coq library name, so a
fully-checked file can be saved to a `.vo` for example.

Don't hesitate to open an issue if you need support for different kind
of URIs in your application / client.

Additionally, `coq-lsp` will use the extension of the file in the URI
to determine the content type. Supported extensions are:
- `.v`: File will be interpreted as a regular Coq vernacular file,
- `.mv`: File will be interpreted as a markdown file, and code
  snippets between `coq` markdown code blocks will be interpreted as
  Coq code.

## Extensions to the LSP specification

As of today, `coq-lsp` implements two extensions to the LSP spec. Note
that none of them are stable yet:

### Goal Display

In order to display proof goals, `coq-lsp` supports the `proof/goals` request, parameters are:
```typescript
interface GoalRequest {
    textDocument: VersionedTextDocumentIdentifier;
    position: Position;
}
```

Answer to the request is a `Goal[]` object, where
```typescript
interface Hyp<Pp> {
  names: Pp[];
  def?: Pp;
  ty: Pp;
}

interface Goal<Pp> {
  hyps: Hyp<Pp>[];
  ty: Pp;
}

interface GoalConfig<Pp> {
  goals : Goal<Pp>[];
  stack : [Goal<Pp>[], Goal<Pp>[]][];
  bullet ?: Pp;
  shelf : Goal<Pp>[];
  given_up : Goal<Pp>[];
}

export interface Message<Pp> {
  range?: Range;
  level : number;
  text : Pp
}

interface GoalAnswer<Pp> {
  textDocument: VersionedTextDocumentIdentifier;
  position: Position;
  goals?: GoalConfig<Pp>;
  messages: Pp[] | Message<Pp>[];
  error?: Pp;
}
```

which can be then rendered by the client in way that is desired.

The main objects of interest are:
- `Hyp`: This represents a pair of hypothesis names and type,
  additionally with a body as obtained with `set` or `pose` tactics
- `Goal`: Contains a Coq goal: a pair of hypothesis and the goal's type
- `GoalConfig`: This is the main object for goals information, `goals`
  contains the current list of foreground goals, `stack` contains a
  list of focused goals, where each element of the list represents a
  focus position (like a zipper); see below for an example. `shelf`
  and `given_up` contain goals in the `shelf` (a kind of goal hiding
  from tactics) and admitted ones.
- `GoalAnswer`: In addition to the goals at point, `GoalAnswer`
  contains messages associated to this position and the top error if pertinent.

An example for `stack` is the following Coq script:
```coq
t. (* Produces 5 goals *)
- t1.
- t2.
- t3. (* Produces 3 goals *)
  + f1.
  + f2. (* <- current focus *)
  + f3.
- t4.
- t5.
```
In this case, the stack will be `[ ["f1"], ["f3"] ; [ "t2"; "t1" ], [ "t4" ; "t5" ]]`.

`proof/goals` was first used in the lambdapi-lsp server
implementation, and we adapted it to `coq-lsp`.

#### Changelog

- v0.1.5: message type does now include range and level
- v0.1.4: goal type generic, the `stacks` and `def` fields appear, compatible v0.1.3 clients
- v0.1.3: send full goal configuration with shelf, given_up, versioned identifier for document
- v0.1.2: include messages and optional error in the request response
- v0.1.1: include position and document in the request response
- v0.1.0: initial version, imported from lambdapi-lsp

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

- v0.1.1: exact copy from Lean protocol (spec under Apache License)
