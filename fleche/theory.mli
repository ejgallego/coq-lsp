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
  val maybe_check : io:Io.CallBack.t -> (Int.Set.t * Doc.t) option
end

(** Create a document inside a theory *)
val create :
     io:Io.CallBack.t
  -> env:Doc.Env.t
  -> uri:Lang.LUri.File.t
  -> raw:string
  -> version:int
  -> unit

(** Update a document inside a theory, returns the list of not valid requests *)
val change :
     io:Io.CallBack.t
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
    | Now of Doc.t
    | Postpone
    | Cancel

  (** Add a request to be served; returns [Postpone] if request is added to the
      queue, [Now doc] if the request is available. [Cancel] means "we will
      never be able to serve this" *)
  val add : t -> action

  (** Removes the request from the list of things to wake up *)
  val remove : t -> unit
end

(* Experimental plugin API, not stable yet *)
module Register : sig
  module Completed : sig
    type t = io:Io.CallBack.t -> doc:Doc.t -> unit
  end

  val add : Completed.t -> unit
end
