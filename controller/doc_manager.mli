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
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Check : sig
  (** Check pending documents, return [None] if there is none pending, or
      [Some rqs] the list of requests ready to execute after the check. Sends
      progress and diagnostics notifications using output function [ofn]. *)
  val maybe_check :
    ofn:(Yojson.Safe.t -> unit) -> concise:bool ->(Int.Set.t * Fleche.Doc.t) option
end

(** Create a document *)
val create :
     ofn:(Yojson.Safe.t -> unit)
  -> root_state:Coq.State.t
  -> workspace:Coq.Workspace.t
  -> uri:Lang.LUri.File.t
  -> raw:string
  -> version:int
  -> unit

(** Update a document, returns the list of not valid requests *)
val change :
     ofn:(Yojson.Safe.t -> unit)
  -> uri:Lang.LUri.File.t
  -> version:int
  -> raw:string
  -> Int.Set.t

(** Close a document *)
val close : uri:Lang.LUri.File.t -> unit

module Request : sig
  type request =
    | FullDoc of { uri : Lang.LUri.File.t }
    | PosInDoc of
        { uri : Lang.LUri.File.t
        ; point : int * int
        ; version : int option
        ; postpone : bool
        }

  type t =
    { id : int
    ; request : request
    }

  type action =
    | Now of Fleche.Doc.t
    | Postpone
    | Cancel

  (** Add a request to be served; returns [true] if request is added to the
      queue , [false] if the request can be already answered. *)
  val add : t -> action

  (** Removes the request from the list of things to wake up *)
  val remove : t -> unit
end
