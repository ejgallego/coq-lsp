import {
  VersionedTextDocumentIdentifier,
  Position,
  Range,
} from "vscode-languageserver-types";

export interface Hyp<Pp> {
  names: Pp[];
  def?: Pp;
  ty: Pp;
}

export interface Goal<Pp> {
  ty: Pp;
  hyps: Hyp<Pp>[];
}

export interface GoalConfig<G, Pp> {
  goals: Goal<G>[];
  stack: [Goal<G>[], Goal<G>[]][];
  bullet?: Pp;
  shelf: Goal<G>[];
  given_up: Goal<G>[];
}

export interface Message<Pp> {
  range?: Range;
  level: number;
  text: Pp;
}

export type Id = ["Id", string];

// XXX: Only used in obligations, move them to Range
export interface Loc {
  fname: any;
  line_nb: number;
  bol_pos: number;
  line_nb_last: number;
  bol_pos_last: number;
  bp: number;
  ep: number;
}

export interface Obl {
  name: Id;
  loc?: Loc;
  status: [boolean, any];
  solved: boolean;
}

export interface OblsView {
  opaque: boolean;
  remaining: number;
  obligations: Obl[];
}

export type ProgramInfo = [Id, OblsView][];

export interface GoalAnswer<Goals, Pp> {
  textDocument: VersionedTextDocumentIdentifier;
  position: Position;
  range?: Range;
  goals?: GoalConfig<Goals, Pp>;
  program?: ProgramInfo;
  messages: Pp[] | Message<Pp>[];
  error?: Pp;
}

export interface GoalRequest {
  textDocument: VersionedTextDocumentIdentifier;
  position: Position;
  pp_format?: "Box" | "Pp" | "Str";
  pretac?: string;
  command?: string;
  mode?: "Prev" | "After";
}

export type Pp =
  | ["Pp_empty"]
  | ["Pp_string", string]
  | ["Pp_glue", Pp[]]
  | ["Pp_box", any, Pp]
  | ["Pp_tag", any, Pp]
  | ["Pp_print_break", number, number]
  | ["Pp_force_newline"]
  | ["Pp_comment", string[]];

export type PpString = Pp | string;

export type Box = ["box", string];

export type BoxString = Box | Pp | string;

export interface FlecheDocumentParams {
  textDocument: VersionedTextDocumentIdentifier;
  ast?: boolean;
  goals?: "Box" | "Pp" | "Str";
}

// Status of the document, Yes if fully checked, range contains the last seen lexical token
export interface CompletionStatus {
  status: ["Yes" | "Stopped" | "Failed"];
  range: Range;
}

// Implementation-specific span information, `range` is assured, the
// other parameters will be present when requested in the call For
// goals, we use the printing mode specified at initalization time
export interface SpanInfo<Goals, Pp> {
  range: Range;
  ast?: any;
  goals?: GoalAnswer<Goals, Pp>;
}

export interface FlecheDocument<Goals, Pp> {
  spans: SpanInfo<Goals, Pp>[];
  completed: CompletionStatus;
}

export interface FlecheSaveParams {
  textDocument: VersionedTextDocumentIdentifier;
}

export interface PerfInfo {
  // Original Execution Time (when not cached)
  time: number;
  // Difference in words allocated in the heap using `Gc.quick_stat`
  memory: number;
  // Whether the execution was cached
  cache_hit: boolean;
  // Caching overhead
  time_hash: number;
}

export interface SentencePerfParams<R> {
  range: R;
  info: PerfInfo;
}

export interface DocumentPerfParams<R> {
  textDocument: VersionedTextDocumentIdentifier;
  summary: string;
  timings: SentencePerfParams<R>[];
}

// View messaging interfaces; should go on their own file
export interface RenderGoals {
  method: "renderGoals";
  params: GoalAnswer<BoxString, PpString>;
}

export interface WaitingForInfo {
  method: "waitingForInfo";
  params: GoalRequest;
}

export interface ErrorData {
  textDocument: VersionedTextDocumentIdentifier;
  position: Position;
  message: string;
}

export interface InfoError {
  method: "infoError";
  params: ErrorData;
}

export type CoqMessagePayload = RenderGoals | WaitingForInfo | InfoError;

export interface CoqMessageEvent extends MessageEvent {
  data: CoqMessagePayload;
}

// For perf panel data
export interface PerfUpdate {
  method: "update";
  params: DocumentPerfParams<Range>;
}

export interface PerfReset {
  method: "reset";
}

export type PerfMessagePayload = PerfUpdate | PerfReset;

export interface PerfMessageEvent extends MessageEvent {
  data: PerfMessagePayload;
}

export interface ViewRangeParams {
  textDocument: VersionedTextDocumentIdentifier;
  range: Range;
}

// Server version and status notifications

export interface CoqServerVersion {
  coq: string;
  ocaml: string;
  coq_lsp: string;
}

export interface CoqBusyStatus {
  status: "Busy";
  modname: string;
}

export interface CoqIdleStatus {
  status: "Idle";
  mem: string;
}

export interface CoqStoppedStatus {
  status: "Stopped";
}

export type CoqServerStatus = CoqBusyStatus | CoqIdleStatus | CoqStoppedStatus;

// Petanque types, canonical source agent.mli
export interface PetStartParams {
  uri: string;
  pre_commands: string | null;
  thm: string;
}

export interface PetRunParams {
  st: number;
  tac: string;
}
