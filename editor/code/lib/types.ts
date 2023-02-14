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

export interface GoalConfig<Pp> {
  goals: Goal<Pp>[];
  stack: [Goal<Pp>[], Goal<Pp>[]][];
  bullet?: Pp;
  shelf: Goal<Pp>[];
  given_up: Goal<Pp>[];
}

export interface Message<Pp> {
  range?: Range;
  level: number;
  text: Pp;
}

export interface GoalAnswer<Pp> {
  textDocument: VersionedTextDocumentIdentifier;
  position: Position;
  goals?: GoalConfig<Pp>;
  messages: Pp[] | Message<Pp>[];
  error?: Pp;
}

export interface GoalRequest {
  textDocument: VersionedTextDocumentIdentifier;
  position: Position;
}
