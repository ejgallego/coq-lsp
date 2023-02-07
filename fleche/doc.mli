(************************************************************************)
(* Flèche => document manager: Document                                 *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Node : sig
  module Info : sig
    type t = private
      { cache_hit : bool
      ; parsing_time : float
      ; time : float option
      ; mw_prev : float
      ; mw_after : float
      ; stats : Stats.t  (** Info about cumulative stats *)
      }

    val print : t -> string
  end

  module Message : sig
    type t = Lang.Range.t option * int * Pp.t
  end

  type t = private
    { range : Lang.Range.t
    ; ast : Coq.Ast.t option  (** Ast of node *)
    ; state : Coq.State.t  (** (Full) State of node *)
    ; diags : Lang.Diagnostic.t list  (** Diagnostics associated to the node *)
    ; messages : Message.t list
    ; info : Info.t
    }

  val range : t -> Lang.Range.t
  val ast : t -> Coq.Ast.t option
  val state : t -> Coq.State.t
  val diags : t -> Lang.Diagnostic.t list
  val messages : t -> Message.t list
  val info : t -> Info.t
end

module Completion : sig
  type t = private
    | Yes of Lang.Range.t  (** Location of the last token in the document *)
    | Stopped of Lang.Range.t  (** Location of the last valid token *)
    | Failed of Lang.Range.t  (** Critical failure, like an anomaly *)
end

(** A Flèche document is basically a [node list], which is a crude form of a
    meta-data map [Range.t -> data], where for now [data] is the contents of
    [Node.t]. *)
type t = private
  { uri : string
  ; version : int
  ; contents : Contents.t
  ; root : Coq.State.t
  ; nodes : Node.t list
  ; diags_dirty : bool
  ; completed : Completion.t
  }

(** Return the list of all asts in the doc *)
val asts : t -> Coq.Ast.t list

(** Note, [create] calls Coq but it is not cached in the Memo.t table *)
val create :
     state:Coq.State.t
  -> workspace:Coq.Workspace.t
  -> uri:string
  -> version:int
  -> raw:string
  -> (t, Loc.t) Coq.Protect.R.t

(** Update the contents of a document, updating the right structures for
    incremental checking. *)
val bump_version : version:int -> raw:string -> t -> t Contents.R.t

(** Checking targets, this specifies what we expect check to reach *)
module Target : sig
  type t =
    | End
    | Position of int * int

  (** [reached ~range (line,col)] checks if [(line,col)] are before [range]'s
      end. *)
  val reached : range:Lang.Range.t -> int * int -> bool
end

(** [check ~ofmt ~target ~doc ()], [target] will have Flèche stop after the
    point specified there has been reached. *)
val check : ofmt:Format.formatter -> target:Target.t -> doc:t -> unit -> t
