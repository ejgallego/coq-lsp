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
  (** Check a document, or yield if there is none pending; it will send progress
      and diagnostics notifications to [ofmt]. Will return the list of requests
      that are ready to execute. *)
  val check_or_yield : ofmt:Format.formatter -> Int.Set.t
end

(** Create a document *)
val create :
     root_state:Coq.State.t
  -> workspace:Coq.Workspace.t
  -> uri:string
  -> contents:string
  -> version:int
  -> unit

(** Update a document, returns the list of not valid requests *)
val change : uri:string -> version:int -> contents:string -> Int.Set.t

(** Close a document *)
val close : uri:string -> unit

exception AbortRequest

(** [find_doc ~uri] , raises AbortRequest if [uri] is invalid *)
val find_doc : uri:string -> Fleche.Doc.t

(** Add a request to be served when the document is completed *)
val serve_on_completion : uri:string -> id:int -> unit

(** Add a request to be served when the document point data is available, for
    now, we allow a single request like that. Maybe returns the id of the
    previous request which should now be cancelled. *)
val serve_on_point : uri:string -> id:int -> point:int * int -> unit
