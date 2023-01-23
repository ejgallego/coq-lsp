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

module Types : sig
  module Point : sig
    type t = Fleche.Types.Point.t [@@deriving yojson]
  end

  module Range : sig
    type t = Fleche.Types.Range.t [@@deriving yojson]
  end
end

val mk_diagnostics :
  uri:string -> version:int -> Fleche.Types.Diagnostic.t list -> Yojson.Safe.t

val mk_progress :
  uri:string -> version:int -> Fleche.Progress.Info.t list -> Yojson.Safe.t

module GoalsAnswer : sig
  type t =
    { textDocument : Base.VersionedTextDocument.t
    ; position : Types.Point.t
    ; goals : string JCoq.Goals.reified_goal JCoq.Goals.goals option
    ; messages : string list
    ; error : string option
    }
  [@@deriving yojson]
end

val mk_goals :
     uri:string
  -> version:int
  -> position:Fleche.Types.Point.t
  -> goals:Coq.Goals.reified_pp option
  -> messages:Pp.t list
  -> error:Pp.t option
  -> Yojson.Safe.t

module Location : sig
  type t =
    { uri : string
    ; range : Types.Range.t
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
    ; range : Types.Range.t option
    }
  [@@deriving yojson]
end

module LabelDetails : sig
  type t = { detail : string } [@@deriving yojson]
end

module TextEditReplace : sig
  type t =
    { insert : Types.Range.t
    ; replace : Types.Range.t
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
