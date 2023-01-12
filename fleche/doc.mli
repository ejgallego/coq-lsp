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

(* [node list] is a very crude form of a meta-data map "loc -> data" , where for
   now [data] is only the goals. *)
module Node : sig
  type t = private
    { loc : Loc.t
    ; ast : Coq.Ast.t option  (** Ast of node *)
    ; state : Coq.State.t  (** (Full) State of node *)
    ; diags : Types.Diagnostic.t list  (** Diagnostics associated to the node *)
    ; messages : Coq.Message.t list
    ; memo_info : string
    }

  val loc : t -> Loc.t
  val ast : t -> Coq.Ast.t option
  val state : t -> Coq.State.t
  val diags : t -> Types.Diagnostic.t list
  val messages : t -> Coq.Message.t list
  val memo_info : t -> string
end

module Completion : sig
  type t = private
    | Yes of Loc.t  (** Location of the last token in the document *)
    | Stopped of Loc.t  (** Location of the last valid token *)
    | Failed of Loc.t  (** Critical failure, like an anomaly *)
end

type t = private
  { uri : string
  ; version : int
  ; contents : string
  ; end_loc : int * int * int
  ; root : Coq.State.t
  ; nodes : Node.t list
  ; diags_dirty : bool
  ; completed : Completion.t
  }

(** Note, [create] is not cached in the Memo.t table *)
val create :
     state:Coq.State.t
  -> workspace:Coq.Workspace.t
  -> uri:string
  -> version:int
  -> contents:string
  -> t Coq.Protect.R.t

val bump_version : version:int -> contents:string -> t -> t

(** [check ofmt ~fb_queue ?cutpoint ~doc] if set, [cutpoint] will have Flèche
    stop after the point specified there has been reached. *)
val check : ofmt:Format.formatter -> ?cutpoint:int * int -> doc:t -> unit -> t
