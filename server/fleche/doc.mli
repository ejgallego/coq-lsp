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

  module Message : sig
    type t = Types.Range.t option * int * Pp.t
  end

  type t = private
    { range : Types.Range.t
    ; ast : Coq.Ast.t option  (** Ast of node *)
    ; state : Coq.State.t  (** (Full) State of node *)
    ; diags : Types.Diagnostic.t list  (** Diagnostics associated to the node *)
    ; messages : Message.t list
    ; info : Info.t
    }

  val range : t -> Types.Range.t
  val ast : t -> Coq.Ast.t option
  val state : t -> Coq.State.t
  val diags : t -> Types.Diagnostic.t list
  val messages : t -> Message.t list
  val info : t -> Info.t
end

module Contents : sig
  type t = private
    { raw : string  (** That's the original, unprocessed document text *)
    ; text : string
          (** That's the text to be sent to the prover, already processed,
              encoded in UTF-8 *)
    ; last : Types.Point.t
          (** Last point of [text], you can derive n_lines from here *)
    ; lines : string Array.t  (** [text] split in lines *)
    }
end

module Completion : sig
  type t = private
    | Yes of Types.Range.t  (** Location of the last token in the document *)
    | Stopped of Types.Range.t  (** Location of the last valid token *)
    | Failed of Types.Range.t  (** Critical failure, like an anomaly *)
end

(** A Flèche document is basically a [node list], which is a crude form of a
    meta-data map [Loc.t -> data], where for now [data] is the contents of
    [Node.t]. *)
type t = private
  { uri : string
  ; version : int
  ; contents : Contents.t
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
  -> (t, Loc.t) Coq.Protect.R.t

(** Update the contents of a document, updating the right structures for
    incremental checking. *)
val bump_version : version:int -> contents:string -> t -> t

(** Checking targets, this specifies what we expect check to reach *)
module Target : sig
  type t =
    | End
    | Position of int * int

  (** [reached ~range (line,col)] checks if [(line,col)] are before [range]'s
      end. *)
  val reached : range:Types.Range.t -> int * int -> bool
end

(** [check ~ofmt ~target ~doc ()], [target] will have Flèche stop after the
    point specified there has been reached. *)
val check : ofmt:Format.formatter -> target:Target.t -> doc:t -> unit -> t
