# coq-lsp protocol documentation

## Introduction and preliminaries

`coq-lsp` should be usable by standard LSP clients, however it
implements some extensions tailored to improve Coq-specific use.

As of today, this document is written for the 3.17 version of the LSP specification:
https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification

For documentation on the API of the VSCode/VSCodium `coq-lsp`
extension see the [VSCODE_API](./VSCODE_API.md) file instead.

See also the upstream LSP issue on generic support for Proof
Assistants
https://github.com/microsoft/language-server-protocol/issues/1414

### coq-lsp basic operating model

`coq-lsp` is a bit different from other servers in that checking the
file is often very expensive, so the continuous LSP model can be too
heavy. The philosophy of `coq-lsp` is to treat a Coq document as a
build task, and then check the document under user-request.

Thus, for example when the user requests goals at a given point,
`coq-lsp` will check if the goals are known, otherwise try to check
the required document parts to return answers to the user ASAP.

`coq-lsp` has three main functioning modes (controlled by a regular
parameter):

- _continuous mode_: in this mode, `coq-lsp` will try to complete
  checking of all open files when idle. This mode has shown to be very
  useful in many contexts, for example educational, as it provides
  very low latency.

- _on-demand mode_: in this mode, `coq-lsp` will do nothing when
  idle. This mode for example can be used to simulate the traditional
  "step-based" Coq interaction mode, just have your client request
  goals as the desired step position, `coq-lsp` will execute the
  document up to that point.

- _on-demand mode, with viewport hints_: in this mode, inspired by
  Isabelle, the `coq-lsp` client will inform the server about the
  user's viewport. This mode provides a comfortable compromise between
  latency and CPU usage.

Note that on-demand mode often implies that some requests that require
the full document to be checked, like `documentSymbols`, will return
less complete information.

Also note that it has been hard for us to design an interaction mode
that would fit well all client editors; for example VSCode doesn't
implement progress on some requests that would be very useful for us.

However, the underlying checking engine (`Flèche`) is very flexible,
so don't hesitate to contact with us if your client would want things
in a different way.

### coq-lsp workspace configuration

See the manual for the exact details, but indeed, coq-lsp will try to
auto-configure Coq projects looking for `_CoqProject` files in the LSP
workspace folders sent by the client.

### A minimal client implementation:

In order to implement a minimal, but working `coq-lsp` client, you need to:

- setup a regular LSP client on your side,
- setup the right parameters for `initializationOptions` on `initialize`,
- implement the `coq/goals` request

And that should be it! We recommend next supporting the
`coq/serverStatus` notification, and maybe `coq/viewport` too.

## Language server protocol support table

If a feature doesn't appear here it usually means it is not planned in the short term:

| Method                                | Support | Notes                                                                    |
|---------------------------------------|---------|--------------------------------------------------------------------------|
| `initialize`                          | Partial | We don't obey the advertised client capabilities                         |
| `client/registerCapability`           | No      | Not planned ATM                                                          |
| `$/setTrace`                          | Yes     |                                                                          |
| `$/logTrace`                          | Yes     |                                                                          |
| `window/logMessage`                   | Yes     |                                                                          |
|---------------------------------------|---------|--------------------------------------------------------------------------|
| `textDocument/didOpen`                | Yes     | We can't reuse Memo tables yet                                           |
| `textDocument/didChange`              | Yes     | We only support `TextDocumentSyncKind.Full` for now                      |
| `textDocument/didClose`               | Partial | We'd likely want to save a `.vo` file on close if possible               |
| `textDocument/didSave`                | Partial | Undergoing behavior refinement                                           |
|---------------------------------------|---------|--------------------------------------------------------------------------|
| `notebookDocument/didOpen`            | No      | Planned                                                                  |
|---------------------------------------|---------|--------------------------------------------------------------------------|
| `textDocument/declaration`            | No      | Planned, blocked on upstream issues                                      |
| `textDocument/definition`             | Yes (*) | Uses .glob information which is often incomplete                         |
| `textDocument/references`             | No      | Planned, blocked on upstream issues                                      |
| `textDocument/hover`                  | Yes     | Shows stats, type info, and location of identifiers at point, extensible |
| `textDocument/codeLens`               | No      |                                                                          |
| `textDocument/foldingRange`           | No      |                                                                          |
| `textDocument/documentSymbol`         | Yes     | Sections and modules missing (#322)                                      |
| `textDocument/semanticTokens`         | No      | Planned                                                                  |
| `textDocument/inlineValue`            | No      | Planned                                                                  |
| `textDocument/inlayHint`              | No      | Planned                                                                  |
| `textDocument/completion`             | Partial | Needs more work locally and upstream (#50)                               |
| `textDocument/publishDiagnostics`     | Yes     |                                                                          |
| `textDocument/diagnostic`             | No      | Planned, issue #49                                                       |
| `textDocument/codeAction`             | No      | Planned                                                                  |
| `textDocument/selectionRange`         | Partial | Selection for a point is its span; no parents                            |
|---------------------------------------|---------|--------------------------------------------------------------------------|
| `workspace/diagnostic`                | No      | Planned                                                                  |
| `workspace/workspaceFolders`          | Yes     | Each folder should have a `_CoqProject` file at the root.                |
| `workspace/didChangeWorkspaceFolders` | Yes     |                                                                          |
| `workspace/didChangeConfiguration`    | Yes (*) | We still do a client -> server push, instead of pull                     |
|---------------------------------------|---------|--------------------------------------------------------------------------|

### URIs accepted by coq-lsp

The `coq-lsp` server only accepts `file:///` URIs; moreover, the URIs
sent to the server must be able to be mapped back to a Coq library
name, so a fully-checked file can be saved to a `.vo` for example.

Don't hesitate to open an issue if you need support for different kind
of URIs in your application / client. The client does support
`vsls:///` URIs.

Additionally, `coq-lsp` will use the extension of the file in the URI
to determine the content type. Supported extensions are:
- `.v`: File will be interpreted as a regular Coq vernacular file,
- `.mv`: File will be interpreted as a markdown file. Code
  snippets between `coq` markdown code blocks will be interpreted as
  Coq code.
- `.v.tex` or `.lv`: File will be interpreted as a LaTeX file. Code
  snippets between `\begin{coq}/\end{coq}` LaTeX environments will be
  interpreted as Coq code.

## Extensions to the LSP specification

As of today, `coq-lsp` implements several extensions to the LSP
spec. Note that none of them are stable yet.

- [Extra diagnostics data](#extra-diagnostics-data)
- [Goal display](#goal-display)
- [File checking progress](#file-checking-progress)
- [Document Ast](#document-ast-request)
- [.vo file saving](#vo-file-saving)
- [Performance data notification](#performance-data-notification)
- [Trim cache notification](#trim-cache-notification)
- [Viewport notification](#viewport-notification)
- [Server configuration parameters](#did-change-configuration-and-server-configuration-parameters)
- [Server version notification](#server-version-notification)
- [Server status notification](#server-status-notification)

### Extra diagnostics data

This is enabled if the server-side option `send_diags_extra_data` is
set to `true`. In this case, some diagnostics may come with extra data
in the optional `data` field.

This field is experimental, and it can change without warning. As of
today we offer two kinds of extra information on errors:

- range of the full sentence that displayed the error,
- if the error was on a Require, information about the library that failed.

As of today, this extra data is passed via member parameters
```typescript
// From `prefix` Require `refs`
type failedRequire = {
    prefix ?: qualid
    refs : qualid list
}

type DiagnosticsData = {
    sentenceRange ?: Range;
    failedRequire ?: FailedRequire
}
```

### Goal Display

In order to display proof goals and information at point, `coq-lsp` supports the `proof/goals` request, parameters are:

```typescript
interface GoalRequest {
    textDocument: VersionedTextDocumentIdentifier;
    position: Position;
    pp_format?: 'Pp' | 'Str';
    pretac?: string;
    command?: string;
    mode?: 'Prev' | 'After';
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
  program?: ProgramInfo;
}

const goalReq : RequestType<GoalRequest, GoalAnswer<PpString>, void>
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

#### Selecting an output format

As of today, the output format type parameter `Pp` is controlled by
the server option `pp_type : number`, see `package.json` for different
values. `0` is guaranteed to be `Pp = string`. Prior to 0.1.6 `string`
was the default.

#### Changelog

- v0.1.9: backwards compatible with 0.1.8
  + new optional `mode : "Prev" | "After"` field to indicate desired goal position
  + `command` field, alias of `pretac`, as this is not limited to tactics
- v0.1.8: new optional `pretac` field for post-processing, backwards compatible with 0.1.7
- v0.1.7: program information added, rest of fields compatible with 0.1.6
- v0.1.7: pp_format field added to request, backwards compatible
- v0.1.6: the `Pp` parameter can now be either Coq's `Pp.t` type or `string` (default)
- v0.1.5: message type does now include range and level
- v0.1.4: goal type was made generic, the `stacks` and `def` fields are not null anymore, compatible v0.1.3 clients
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

### Document Ast Request

The `coq/getDocument` request returns a serialized version of Fleche's
document. It is modelled after LSP's standard
`textDocument/documentSymbol`, but returns instead the full document
contents as understood by Flèche.

Caveats: Flèche notion of document is evolving, in particular you
should not assume that the document will remain a list, but it will
become a tree at some point.

```typescript
interface FlecheDocumentParams {
    textDocument: VersionedTextDocumentIdentifier;
}
```

```typescript
// Status of the document, Yes if fully checked, range contains the last seen lexical token
interface CompletionStatus {
    status : ['Yes' | 'Stopped' | 'Failed']
    range : Range
};

// Implementation-specific span information, for now the serialized Ast if present.
type SpanInfo = any;

interface RangedSpan {
    range : Range;
    span?: SpanInfo
};

interface FlecheDocument {
    spans: RangedSpan[];
    completed : CompletionStatus
};

const docReq : RequestType<FlecheDocumentParams, FlecheDocument, void>
```

#### Changelog

- v0.1.6: initial version

### .vo file saving

Coq-lsp provides a file-save request `coq/saveVo`, which will save the
current file to disk.

Note that `coq-lsp` does not automatic trigger this on `didSave`, as
it would produce too much disk trashing, but we are happy to implement
usability tweaks so `.vo` files are produced when they should.

```typescript
interface FlecheSaveParams {
    textDocument: VersionedTextDocumentIdentifier;
}
```

The request will return `null`, or fail if not successful.

#### Changelog

- v0.1.6: first version

### Performance Data Notification

The `$/coq/filePerfData` notification is sent from server to client
when the checking completes (if the server-side `send_perf_data`
option is enabled); it includes information about execution hotspots,
caching, and memory use by sentences:

```typescript
interface PerfInfo {
  // Original Execution Time (when not cached)
  time: number;
  // Difference in words allocated in the heap using `Gc.quick_stat`
  memory: number;
  // Whether the execution was cached
  cache_hit: boolean;
  // Caching overhead
  time_hash: number;
}

interface SentencePerfParams<R> {
  range: R;
  info: PerfInfo;
}

interface DocumentPerfParams<R> {
  textDocument: VersionedTextDocumentIdentifier;
  summary: string;
  timings: SentencePerfParams<R>[];
}

const coqPerfData : NotificationType<DocumentPerfParams<Range>>
```

#### Changelog

- v0.1.9:
  + new server-side option to control whether the notification is sent
  + Fields renamed: `loc -> range`, `mem -> memory`
  + Fixed type for `range`, it was always `Range`
  + `time` and `memory` are now into a better `PerfInfo` data, which
    correctly provides info for memoized sentences
  + We now send the real time, even if the command was cached
  + `memory` now means difference in memory from `GC.quick_stat`
  + `filePerfData` will send the full document, ordered linearly, in
    0.1.7 we only sent the top 10 hotspots
  + generalized typed over `R` parameter for range
- v0.1.8: Spec was accidentally broken, types were invalid
- v0.1.7: Initial version

### Trim cache notification

The `coq/trimCaches` notification from client to server tells the
server to free memory. It has no parameters.

### Viewport notification

The `coq/viewRange` notification from client to server tells the
server the visible range of the user.

```typescript
interface ViewRangeParams {
  textDocument: VersionedTextDocumentIdentifier;
  range: Range;
}
```

### Did Change Configuration and Server Configuration parameters

The server will listen to the `workspace/didChangeConfiguration`
parameters and try to update them without a full server restart.

The `settings` field corresponds to the data structure also passed in
the `initializationOptions` parameter for the LSP `init` method.

As of today, the server exposes the following parameters:

```typescript
export interface CoqLspServerConfig {
  client_version: string;
  eager_diagnostics: boolean;
  goal_after_tactic: boolean;
  show_coq_info_messages: boolean;
  show_notices_as_diagnostics: boolean;
  admit_on_bad_qed: boolean;
  debug: boolean;
  unicode_completion: "off" | "normal" | "extended";
  max_errors: number;
  pp_type: 0 | 1 | 2;
  show_stats_on_hover: boolean;
  show_loc_info_on_hover: boolean;
  check_only_on_request: boolean;
}
```

The settings are documented in the `package.json` file for the VSCode
client.

#### Changelog

- v0.1.9: First public documentation.

### Server Version Notification

The server will send the `$/coq/serverVersion` notification to inform
the client about `coq-lsp` version specific info.

The parameters are:
```typescript
export interface CoqServerVersion {
  coq: string;
  ocaml: string;
  coq_lsp: string;
}
```

#### Changelog

- v0.1.9: First public documentation.

### Server Status Notification

The server will send the `$/coq/serverStatus` notification to inform
the client of checking status (start / end checking file)

The parameters are:
```typescript

export interface CoqBusyStatus {
  status: "Busy";
  modname: string;
}

export interface CoqIdleStatus {
  status: "Idle" | "Stopped";
}

export type CoqServerStatus = CoqBusyStatus | CoqIdleStatus;
```

#### Changelog

- v0.1.9: First public documentation.
