import { VersionedTextDocumentIdentifier } from "vscode-languageclient";
import { Position } from "vscode";

export interface Hyp<Pp> {
  names: Pp;
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

export interface GoalAnswer<Pp> {
  textDocument: VersionedTextDocumentIdentifier;
  position: Position;
  goals?: GoalConfig<Pp>;
  messages: Pp[];
  error?: Pp;
}

export interface GoalRequest {
  textDocument: VersionedTextDocumentIdentifier;
  position: Position;
}
