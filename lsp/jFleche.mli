(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Config : sig
  type t = Fleche.Config.t [@@deriving yojson]
end

val mk_progress :
     uri:Lang.LUri.File.t
  -> version:int
  -> Fleche.Progress.Info.t list
  -> Yojson.Safe.t

module Message : sig
  type 'a t =
    { range : JLang.Range.t option
    ; level : int
    ; text : 'a
    }
end

module GoalsAnswer : sig
  type 'pp t =
    { textDocument : Doc.VersionedTextDocument.t
    ; position : Lang.Point.t
    ; goals : 'pp Coq.Goals.reified_pp option
    ; messages : 'pp Message.t list
    ; error : 'pp option [@default None]
    }
  [@@deriving to_yojson]
end

module Location : sig
  type t =
    { uri : Lang.LUri.File.t
    ; range : Lang.Range.t
    }
  [@@deriving yojson]
end

(** {1 document/definition} *)
module LocationLink : sig
  type t =
    { originSelectionRange : Lang.Range.t option [@default None]
    ; targetUri : Lang.LUri.File.t
    ; targetRange : Lang.Range.t
    ; targetSelectionRange : Lang.Range.t
    }
  [@@deriving yojson]
end

(** {1 DocumentSymbols} *)

module DocumentSymbol : sig
  type t =
    { name : string
    ; detail : string option [@default None]
    ; kind : int
    ; tags : int list option [@default None]
    ; deprecated : bool option [@default None]
    ; range : Lang.Range.t
    ; selectionRange : Lang.Range.t
    ; children : t list option [@default None]
    }
  [@@deriving yojson]
end

(** Not used as of today, superseded by DocumentSymbol *)
module SymInfo : sig
  type t =
    { name : string
    ; kind : int
    ; location : Location.t
    }
  [@@deriving yojson]
end

(** {1 Hover} *)

module HoverContents : sig
  type t =
    { kind : string
    ; value : string
    }
  [@@deriving yojson]
end

module HoverInfo : sig
  type t =
    { contents : HoverContents.t
    ; range : Lang.Range.t option [@default None]
    }
  [@@deriving yojson]
end

(** {1 Completion} *)

module LabelDetails : sig
  type t = { detail : string } [@@deriving yojson]
end

module TextEditReplace : sig
  type t =
    { insert : Lang.Range.t
    ; replace : Lang.Range.t
    ; newText : string
    }
  [@@deriving yojson]
end

module CompletionData : sig
  type t =
    { label : string
    ; insertText : string option [@default None]
    ; labelDetails : LabelDetails.t option [@default None]
    ; textEdit : TextEditReplace.t option [@default None]
    ; commitCharacters : string list option [@default None]
    }
  [@@deriving yojson]
end

(** Coq-lsp-specific *)
module CompletionStatus : sig
  type t =
    { status : [ `Yes | `Stopped | `Failed ]
    ; range : Lang.Range.t
    }
  [@@deriving yojson]
end

module RangedSpan : sig
  type t =
    { range : Lang.Range.t
    ; span : Coq.Ast.t option [@default None]
    }
  [@@deriving to_yojson]
end

module FlecheDocument : sig
  type t =
    { spans : RangedSpan.t list
    ; completed : CompletionStatus.t
    }
  [@@deriving to_yojson]
end

(** Pull Diagnostics *)
module DocumentDiagnosticParams : sig
  type t =
    { textDocument : string
    ; indentifier : string option [@default None]
    ; previousResultId : string option [@default None]
    ; workDoneToken : Base.ProgressToken.t option [@default None]
    ; partialResultToken : Base.ProgressToken.t option [@default None]
    }
  [@@deriving of_yojson]
end

module FullDocumentDiagnosticReport : sig
  type t =
    { kind : string
    ; resultId : string option [@default None]
    ; items : JLang.Diagnostic.t list
          (* relatedDocuments to be added in 0.2.x *)
    }
  [@@deriving to_yojson]
end

module UnchangedDocumentDiagnosticReport : sig
  type t =
    { kind : string
    ; resultId : string option [@default None]
    }
  [@@deriving to_yojson]
end

(** partial result: The first literal send need to be a DocumentDiagnosticReport
    followed by n DocumentDiagnosticReportPartialResult literals defined as
    follows: *)
module DocumentDiagnosticReportPartialResult : sig
  type t =
    { relatedDocuments :
        (Lang.LUri.File.t * FullDocumentDiagnosticReport.t) list
    }
  [@@deriving to_yojson]
end
