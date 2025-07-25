# coq-lsp protocol documentation

## Table of contents

<!-- TOC start (generated with https://github.com/derlin/bitdowntoc) -->
 - [Introduction and preliminaries](#introduction-and-preliminaries)
    * [coq-lsp basic operating model](#coq-lsp-basic-operating-model)
    * [coq-lsp workspace configuration](#coq-lsp-workspace-configuration)
    * [A minimal client implementation:](#a-minimal-client-implementation)
 - [Language server protocol support table](#language-server-protocol-support-table)
    * [URIs accepted by coq-lsp](#uris-accepted-by-coq-lsp)
 - [Implementation-specific options](#implementation-specific-options)
 - [Implementation-specific `data` error field](#implementation-specific-data-error-field)
 - [Extensions to the LSP specification](#extensions-to-the-lsp-specification)
    * [Extra diagnostics data](#extra-diagnostics-data)
    * [Goal Display](#goal-display)
    * [File checking progress](#file-checking-progress)
    * [Document Ast Request](#document-ast-request)
    * [.vo file saving](#vo-file-saving)
    * [Performance Data Notification](#performance-data-notification)
    * [Trim cache notification](#trim-cache-notification)
    * [Viewport notification](#viewport-notification)
    * [Did Change Configuration and Server Configuration parameters](#did-change-configuration-and-server-configuration-parameters)
    * [Server Version Notification](#server-version-notification)
    * [Server Status Notification](#server-status-notification)
 - [Pétanque](#pétanque)
    * [Changelog](#changelog-8)
    * [Common types](#common-types)
    * [`petanque/get_root_state`:](#petanqueget_root_state)
    * [`petanque/get_state_at_pos`](#petanqueget_state_at_pos)
    * [`petanque/start`](#petanquestart)
    * [`petanque/run`](#petanquerun)
    * [`petanque/goals`](#petanquegoals)
    * [`petanque/premises`](#petanquepremises)
    * [`petanque/state/eq`](#petanquestateeq)
    * [`petanque/state/hash`](#petanquestatehash)
    * [`petanque/state/proof/equal`](#petanquestateproofequal)
    * [`petanque/state/proof/hash`](#petanquestateproofhash)
    * [`petanque/ast`](#petanqueast)
    * [`petanque/ast_at_post`](#petanqueastatpos)

<!-- TOC end -->

<!-- TOC --><a name="introduction-and-preliminaries"></a>
## Introduction and preliminaries

`coq-lsp` is a Language Server Protocol implementation for the Rocq
Prover. It is compatible with standard LSP clients but includes
extensions for advanced Rocq-specific, machine-learning, and software
engineering workflows, named `petanque`.

This document is written for the 3.17 version of the LSP specification:
https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification

For documentation on the API of the VSCode/VSCodium `coq-lsp`
extension see the [VSCODE_API](./VSCODE_API.md) file instead.

See also the upstream LSP issue on generic support for Proof
Assistants
https://github.com/microsoft/language-server-protocol/issues/1414

<!-- TOC --><a name="coq-lsp-basic-operating-model"></a>
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
  idle. This mode, for example, can simulate the traditional
  "step-based" Rocq interaction mode, configure your client to request
  goals at the desired position, and `coq-lsp` will execute the
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
please feel free to contact with us if your client would want things
in a different way.

<!-- TOC --><a name="coq-lsp-workspace-configuration"></a>
### coq-lsp workspace configuration

See the manual for the exact details. By default, `coq-lsp` attempts
to auto-configure projects by locating `_CoqProject` files within the
LSP workspace folders sent by the client.

<!-- TOC --><a name="a-minimal-client-implementation"></a>
### A minimal client implementation:

To implement a minimal but functional `coq-lsp` client, you need to:

- Initialize a standard LSP client.
- Setup the right parameters for `initializationOptions` on `initialize`.
- Implement the `coq/goals` request handler.

Optionally, we recommend supporting:

- The `coq/serverStatus` notification.
- The `coq/viewport` notification.

<!-- TOC --><a name="language-server-protocol-support-table"></a>
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

<!-- TOC --><a name="uris-accepted-by-coq-lsp"></a>
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

<!-- TOC --><a name="implementation-specific-options"></a>
## Implementation-specific options

The `coq-lsp` server accepts several options via the
`initializationOptions` field of the LSP initialize request. See
`package.json` and the documentation of the
`workspace/didChangeConfiguration` call below for the list of options.

<!-- TOC --><a name="implementation-specific-data-error-field"></a>
## Implementation-specific `data` error field

Rocq will often generate "feedback" messages when trying to execute
commands, for example debug messages, or to return solutions to
commands such as `Search` or `Print`.

Rocq "feedback" is very context dependent, feedback related to
document sentences is recorded in the document, and can be obtained
with the `coq/goals` request below.

Feedback related to specific command requests is handled via:

- if the request succeeds, feedback should be reflected in the return type of the request
- if the request fails, we will set the optional `data` field in the
  request response to an object of type `RocqErrorData`:
```
interface RocqErrorData = {
  feedback : Message<string>[];
  }
```

<!-- TOC --><a name="extensions-to-the-lsp-specification"></a>
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

<!-- TOC --><a name="extra-diagnostics-data"></a>
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

<!-- TOC --><a name="goal-display"></a>
### Goal Display

In order to display proof goals and information at point, `coq-lsp`
supports the `proof/goals` request, parameters are:

```typescript
interface GoalRequest {
    textDocument: VersionedTextDocumentIdentifier;
    position: Position;
    pp_format?: 'Pp' | 'Str';
    command?: string;
    mode?: 'Prev' | 'After';
}
```

The `textDocument` and `position` parameters are standard.

Note that `rocq-lsp` will execute the Rocq document up to the
`position` specified in the request paremeters.

- `pp_format` controls the pretty printing format used in the
  results. `Pp` will return goals using Rocq's pretty-printing type
  (to be documented, see our rendered under
  `editor/code/lib/format-pprint`), `String` will return the goals and
  message bodies in plain text.

- `command`, is a list of Coq commands that will be run just _after_
  `position` in `textDocument`, but _before_ goals are sent to the
  user. This is often useful for ephemeral post-processing of goals.

- `mode` (if absent, the `goal_after_tactic` parameter will be used)
  controls whether the goals returned correspond to `position` or to
  the previous sentence in the document. `messages` and `error` below
  are always returned for the specified `position`.

The answer to the `proof/goals` request is a `GoalAnswer` object,
where:

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
  range?: Range;
  goals?: GoalConfig<Pp>;
  messages: Pp[] | Message<Pp>[];
  error?: Pp;
  program?: ProgramInfo;
}

const goalReq : RequestType<GoalRequest, GoalAnswer<PpString>, void>
```

which can be then rendered by the client at wish.

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

  If `mode` was set to `Prev`, or the `goal_after_tactic` option is
  set to `false`, goals returned here will correspond to the previous
  sentence.

- `GoalAnswer`: In addition to the goals at point, `GoalAnswer`
  contains messages associated to `position` and the top `error` if
  pertinent. `range` contains the span of the Rocq sentence at
  `position`, if exists. Note that Rocq will skip some blank spaces
  when parsing, so there are parts of a document that have no
  corresponding `range` attached.

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

<!-- TOC --><a name="selecting-an-output-format"></a>
#### Selecting an output format

As of today, the output format type parameter `Pp` is controlled by
the server option `pp_type : number`, see `package.json` for different
values. `0` is guaranteed to be `Pp = string`. Prior to 0.1.6 `string`
was the default.

<!-- TOC --><a name="changelog"></a>
#### Changelog

- v0.2.3: new field in answer `range`, which contains the range of the
  sentence at `position`
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

<!-- TOC --><a name="file-checking-progress"></a>
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

<!-- TOC --><a name="changelog-1"></a>
#### Changelog

- v0.1.1: exact copy from Lean protocol (spec under Apache License)

<!-- TOC --><a name="document-ast-request"></a>
### Document Ast Request

The `coq/getDocument` request returns a serialized version of Fleche's
document, plus some additional information for each sentence / node.

It is modelled after LSP's standard `textDocument/documentSymbol`, but
returns instead the full document contents as understood by Flèche.

Caveats: Flèche notion of document is evolving, in particular you
should not assume that the document will remain a list, more structure
could be happening..

```typescript
interface FlecheDocumentParams {
    textDocument: VersionedTextDocumentIdentifier;
    ast ?: boolean;
    goals ?: 'Pp' | 'Str';
}
```

```typescript
// Status of the document, Yes if fully checked, range contains the last seen lexical token
interface CompletionStatus {
    status : ['Yes' | 'Stopped' | 'Failed']
    range : Range
};

// Implementation-specific span information, `range` is assured, the
// other parameters will be present when requested in the call For
// goals, we use the printing mode specified at initalization time
interface SpanInfo {
    range : Range;
    ast ?: any;
    goals ?: GoalsAnswer<Pp>;
};

interface FlecheDocument {
    spans: RangedSpan[];
    completed : CompletionStatus
};

const docReq : RequestType<FlecheDocumentParams, FlecheDocument, void>
```

<!-- TOC --><a name="changelog-2"></a>
#### Changelog

- v0.1.6: initial version

<!-- TOC --><a name="vo-file-saving"></a>
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

<!-- TOC --><a name="changelog-3"></a>
#### Changelog

- v0.2.4: non-backwards compatible change! `RangedSpan` type is
  removed in favor of `SpanInfo`. `SpanInfo` now contains a list of
  properties, for now `range`, `ast`, `goals`, which are returned
  depending on the request parameters, except for `range` which is
  always present. New (optional) fields `ast` and `goals` are added to
  `FlecheDocumentParams`.
- v0.1.6: first version

<!-- TOC --><a name="performance-data-notification"></a>
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

<!-- TOC --><a name="changelog-4"></a>
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

<!-- TOC --><a name="trim-cache-notification"></a>
### Trim cache notification

The `coq/trimCaches` notification from client to server tells the
server to free memory. It has no parameters.

<!-- TOC --><a name="viewport-notification"></a>
### Viewport notification

The `coq/viewRange` notification from client to server tells the
server the visible range of the user.

```typescript
interface ViewRangeParams {
  textDocument: VersionedTextDocumentIdentifier;
  range: Range;
}
```

<!-- TOC --><a name="did-change-configuration-and-server-configuration-parameters"></a>
### Did Change Configuration and Server Configuration parameters

The server will listen to the `workspace/didChangeConfiguration`
parameters and try to update them without a full server restart.

The `settings` field corresponds to the data structure also passed in
the `initializationOptions` parameter for the LSP `init` method.

As of today, the server exposes the following parameters:

```typescript
export interface UnicodeCompletionConfig {
    enabled: "off" | "normal" | "extended";
    commit_chars : string[];
}

export interface CompletionConfig {
    unicode: UnicodeCompletionConfig
}

export interface CoqLspServerConfig {
  client_version: string;
  eager_diagnostics: boolean;
  goal_after_tactic: boolean;
  show_coq_info_messages: boolean;
  show_notices_as_diagnostics: boolean;
  admit_on_bad_qed: boolean;
  debug: boolean;
  unicode_completion: "off" | "normal" | "extended"; // Deprecated
  max_errors: number;
  pp_type: 0 | 1 | 2;
  show_stats_on_hover: boolean;
  show_loc_info_on_hover: boolean;
  show_universes_on_hover: boolean;
  show_state_hash_on_hover: boolean;
  check_only_on_request: boolean;
  send_perf_data: boolean;
  completion: CompletionConfig
}
```

The settings are documented in the `package.json` file for the VSCode
client.

<!-- TOC --><a name="changelog-5"></a>
#### Changelog

- v0.2.4:
  + Deprecate `unicode_completion` in favor of new `completion:
    CompletionConfig` configuration record.
- v0.2.3: New options, `show_universes_on_hover`,
  `show_state_hash_on_hover`, `send_perf_data`.
- v0.1.9: First public documentation.

<!-- TOC --><a name="server-version-notification"></a>
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

<!-- TOC --><a name="changelog-6"></a>
#### Changelog

- v0.1.9: First public documentation.

<!-- TOC --><a name="server-status-notification"></a>
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

<!-- TOC --><a name="changelog-7"></a>
#### Changelog

- v0.1.9: First public documentation.

<!-- TOC --><a name="pétanque"></a>
## Pétanque

The `pétanque` API enables lightweight interaction with Rocq without
requiring modifications to the document. This is very useful in
various contexts, especially for accessing Rocq's command command
execution and proof engine. `pétanque` uses the same JSON-RPC 2.0
protocol as LSP.

`pétanque` is at an experimental stage, and can be used as a standalone
tool via the `pet-server` binary. We strongly recommend to use `pétanque`
withing an LSP context.

Several resource-heavy server-side Rocq objects such as proof states
are represented in the protocol via integer identifiers, as they
cannot be serialized practically. These will be garbage collected
automatically in future versions of the API.

Preliminary documentation for `pétanque` is provided below:

<!-- TOC --><a name="changelog-8"></a>
### Changelog

- v1 (coq-lsp 0.2.3): Initial public release
- v2 (coq-lsp 0.2.4):
  + **added**: new methods for Ast access
    [`petanque/ast`](#petanqueast) and
    [`petanque/ast_at_pos`](#petanqueastatpos) (@ejgallego, @JulesViennotFranca, #980)
  + **changed**: `No_state_at_point` error is now `No_node_at_point` (@JulesViennotFranca, #980)

### Pétanque basics

The basic operating mode of petanque is to first get a **Rocq state**
from a document, this can be done either by position, or via a lemma
name. Once you have a state at hand, you can use `petanque/run` to
execute a Rocq command, `petanque/goals` to obtain goals from it, and
a variety of other operations.

<!-- TOC --><a name="common-types"></a>
### Common types

Options for command execution, in particular, whether to memoize the
execution and whether to hash it:

```typescript
interface Run_opts {
    { memo ?: bool [@default true]
    ; hash ?: bool [@default true]
    }
end
```

Result of a Rocq command execution. Contains a result, a hash of the
result (if enabled), whether the resulting command finished a proof,
and Rocq feedback messages generated by the execution of the command.

```typescript
interface Run_result<res> {
  { st : res
  ; hash ?: int
  ; proof_finished : bool
  ; feedback : (int * string) list
  }
```

<!-- TOC --><a name="petanqueget_root_state"></a>
### `petanque/get_root_state`:

Returns state at the beginning of a document. Forces execution of the
full document.

```typescript
interface Params =
    { uri : string
    ; opts ?: Run_opts
    }
```

```typescript
interface Response = Run_result<number>
```

<!-- TOC --><a name="petanqueget_state_at_pos"></a>
### `petanque/get_state_at_pos`

Returns state at a given document point. Will force execution of the
document to that point. Recall that [LSP
positions](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#position)
are zero-based, (line 1 in editors is line 0 here).

```typescript
interface Params =
    { uri : string
    ; opts ?: Run_opts
    ; position : Position
    }
```

```typescript
interface Response = Run_result<int>
}
```

<!-- TOC --><a name="petanquestart"></a>
### `petanque/start`

Returns the state corresponding after the start of a lemma (that is to
say, before any proofs). Forces the execution of the full document.

`thm` is the theorem name to prove, note that we don't handle aliases
well yet, `pre_commands` can be used to inject commands _before_ the
lemma declaration.

```typescript
interface Params =
    { uri : string
    ; opts ?: Run_opts
    ; pre_commands ?: string
    ; thm : string
    }
```

```typescript
interface Response = Run_result<number>
```

<!-- TOC --><a name="petanquerun"></a>
### `petanque/run`

Runs Rocq commands (either tactics or a full commands). It admits
multiple commands, separated by the usual `.`.

```typescript
interface Params =
    { opts ?: Run_opts
    ; st: number
    ; tac: string
    }
```

```typescript
interface Response = Run_result<int>
```

If the execution fails, the JSON-RPC request will fail.

<!-- TOC --><a name="petanquegoals"></a>
### `petanque/goals`

```typescript
interface Params = { st: number }
```

```typescript
interface Response = GoalConfig<string>
```

<!-- TOC --><a name="petanquepremises"></a>
### `petanque/premises`

Returns information about declared Rocq objects at a particular state:

```typescript
interface Params = { st: number }
```

```typescript
interface Info =
      { kind : string /* type of object */
      ; range ?: Range /* a range, if known */
      ; offset : int * int   /* a offset in the file */
      ; raw_text : Result<string, string> /* raw text of the premise */
      }

interface Premise =
    { full_name : string
          /* should be a Coq DirPath, but let's go step by step */
    ; file : string /* file (in FS format) where the premise is found */
    ; info : Result<Info, string> /* Info about the object, if available */
    }

interface Response = Premise
```

<!-- TOC --><a name="petanquestateeq"></a>
### `petanque/state/eq`

Checks equality of states, with `petanque/state/hash` it can be used
to implement a client-side hash table of visited proof states.

```typescript
interface Inspect =
 | Physical  /** Flèche-based "almost physical" state eq */
 | Goals /** Full goal equality, much faster than calling goals, but still linear on the side of the goal type and context */

interface Params =
      { kind ?: Inspect
      ; st1 : int
      ; st2 : int
      }
```

```typescript
interface Response = bool
```

<!-- TOC --><a name="petanquestatehash"></a>
### `petanque/state/hash`

Hash for a Rocq state. Note we use a quick hash, so on collisions, `petanque/state/eq` must be used.

```typescript
interface Params = { st: number }
```

```typescript
interface Response = number
```

<!-- TOC --><a name="petanquestateproofequal"></a>
### `petanque/state/proof/equal`

Version of `petanque/state/equal` but only for the proof state.

<!-- TOC --><a name="petanquestateproofhash"></a>
### `petanque/state/proof/hash`

Version of `petanque/state/hash` but only for the proof state.

<!-- TOC --><a name="petanqueast"></a>
### `petanque/ast`

Parse a string. `Ast` is a JSON serialization of Rocq's Ast, as in
`coq/getDocument`, and often not stable between versions.

```typescript
interface Params = { st: int; text : string }
```

```typescript
interface Response = Run_result<Option<Ast>>
```

<!-- TOC --><a name="petanqueastatpos"></a>
### `petanque/ast_at_pos`

Return Rocq's `Ast` at point. Note that:

- if no node is at `position`, then we error
- if there is a node, but not Ast (due to a parsing error for
  example), we return `None`

```typescript
interface Params = { uri: string; position : Position }
```

```typescript
interface Response = Option<Ast>
```
