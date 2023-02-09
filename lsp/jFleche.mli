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

module GoalsAnswer : sig
  type t =
    { textDocument : Doc.VersionedTextDocument.t
    ; position : Lang.Point.t
    ; goals : string JCoq.Goals.reified_goal JCoq.Goals.goals option
    ; messages : string list
    ; error : string option
    }
  [@@deriving yojson]
end

val mk_goals :
     uri:Lang.LUri.File.t
  -> version:int
  -> position:Lang.Point.t
  -> goals:Coq.Goals.reified_pp option
  -> messages:Pp.t list
  -> error:Pp.t option
  -> Yojson.Safe.t

module Location : sig
  type t =
    { uri : Lang.LUri.File.t
    ; range : Lang.Range.t
    }
  [@@deriving yojson]
end

module SymInfo : sig
  type t =
    { name : string
    ; kind : int
    ; location : Location.t
    }
  [@@deriving yojson]
end

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
    ; range : Lang.Range.t option
    }
  [@@deriving yojson]
end

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
    ; insertText : string option
    ; labelDetails : LabelDetails.t option
    ; textEdit : TextEditReplace.t option
    ; commitCharacters : string list option
    }
  [@@deriving yojson]
end
