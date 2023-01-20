import {
  TextDocumentIdentifier,
  VersionedTextDocumentIdentifier,
} from "vscode-languageclient";
import { Position } from "vscode";

export interface Hyp {
  names: string;
  ty: string;
}

export interface Goal {
  ty: string;
  hyps: Hyp[];
}

export interface GoalRequest {
  textDocument: TextDocumentIdentifier;
  position: Position;
}

export interface GoalConfig {
  goals: Goal[];
  stack: undefined;
  bullet?: string;
  shelf: Goal[];
  given_up: Goal[];
}
export interface GoalAnswer {
  textDocument: VersionedTextDocumentIdentifier;
  position: Position;
  goals?: GoalConfig;
  messages: string[];
  error?: string;
}
