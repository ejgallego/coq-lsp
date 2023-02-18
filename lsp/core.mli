(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(** Core LSP protocoal and language types *)

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
