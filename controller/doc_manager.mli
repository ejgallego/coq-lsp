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
      progress and diagnostics notifications to [ofmt]. *)
  val maybe_check : ofmt:Format.formatter -> Int.Set.t option
end

(** Create a document *)
val create :
     ofmt:Format.formatter
  -> root_state:Coq.State.t
  -> workspace:Coq.Workspace.t
  -> uri:string
  -> raw:string
  -> version:int
  -> unit

(** Update a document, returns the list of not valid requests *)
val change :
  ofmt:Format.formatter -> uri:string -> version:int -> raw:string -> Int.Set.t

(** Close a document *)
val close : uri:string -> unit

exception AbortRequest

(** [find_doc ~uri] , raises AbortRequest if [uri] is invalid *)
val find_doc : uri:string -> Fleche.Doc.t

(** Add a request to be served when the document is completed *)
val add_on_completion : uri:string -> id:int -> unit

val remove_on_completion : uri:string -> id:int -> unit

(** Add a request to be served when the document point data is available, for
    now, we allow a single request like that. Maybe returns the id of the
    previous request which should now be cancelled. *)
val add_on_point : uri:string -> id:int -> point:int * int -> unit

val remove_on_point : uri:string -> id:int -> point:int * int -> unit
