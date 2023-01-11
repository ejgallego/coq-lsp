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
  type t =
    { textDocument : Doc.VersionedTextDocument.t
    ; position : Lang.Point.t
    ; goals : string JCoq.Goals.reified_goal JCoq.Goals.goals option
    ; messages : string Message.t list
    ; error : string option [@default None]
    }
  [@@deriving to_yojson]
end

val mk_goals :
     uri:Lang.LUri.File.t
  -> version:int
  -> position:Lang.Point.t
  -> goals:Coq.Goals.reified_pp option
  -> messages:Pp.t Message.t list
  -> error:Pp.t option
  -> Yojson.Safe.t

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
module Location : sig
  type t =
    { uri : Lang.LUri.File.t
    ; range : Lang.Range.t
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
