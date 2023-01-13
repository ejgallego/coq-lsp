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
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

module Node : sig
  module Info : sig
    type t = private
      { cache_hit : bool
      ; parsing_time : float
      ; time : float option
      ; mw_prev : float
      ; mw_after : float
      }

    val print : stats:Stats.t -> t -> string
  end

  type t = private
    { loc : Loc.t
    ; ast : Coq.Ast.t option  (** Ast of node *)
    ; state : Coq.State.t  (** (Full) State of node *)
    ; diags : Types.Diagnostic.t list  (** Diagnostics associated to the node *)
    ; messages : Coq.Message.t list
    ; info : Info.t
    }

  val loc : t -> Loc.t
  val ast : t -> Coq.Ast.t option
  val state : t -> Coq.State.t
  val diags : t -> Types.Diagnostic.t list
  val messages : t -> Coq.Message.t list
  val info : t -> Info.t
end

module Completion : sig
  type t = private
    | Yes of Loc.t  (** Location of the last token in the document *)
    | Stopped of Loc.t  (** Location of the last valid token *)
    | Failed of Loc.t  (** Critical failure, like an anomaly *)
end

(** A Flèche document is basically a [node list], which is a crude form of a
    meta-data map [Loc.t -> data], where for now [data] is the contents of
    [Node.t]. *)
type t = private
  { uri : string
  ; version : int
  ; contents : string
  ; end_loc : Types.Point.t
  ; root : Coq.State.t
  ; nodes : Node.t list
  ; diags_dirty : bool
  ; completed : Completion.t
  ; stats : Stats.t  (** Info about cumulative document stats *)
  }

(** Note, [create] calls Coq but it is not cached in the Memo.t table *)
val create :
     state:Coq.State.t
  -> workspace:Coq.Workspace.t
  -> uri:string
  -> version:int
  -> contents:string
  -> t Coq.Protect.R.t

(** Update the contents of a document, updating the right structures for
    incremental checking. *)
val bump_version : version:int -> contents:string -> t -> t

(** Checking targets, this specifies what we expect check to reach *)
module Target : sig
  type t =
    | End
    | Position of int * int
end

(** [check ofmt ~fb_queue ?cutpoint ~doc] if set, [cutpoint] will have Flèche
    stop after the point specified there has been reached. *)
val check : ofmt:Format.formatter -> target:Target.t -> doc:t -> unit -> t
