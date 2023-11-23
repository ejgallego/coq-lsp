(************************************************************************)
(* Flèche => document manager: Document                                 *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Node : sig
  module Ast : sig
    type t =
      { v : Coq.Ast.t
      ; ast_info : Lang.Ast.Info.t list option
      }
  end

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
    type t = Lang.Range.t option * Lang.Diagnostic.Severity.t * Pp.t
  end

  type t = private
    { range : Lang.Range.t
    ; ast : Ast.t option  (** Ast of node *)
    ; state : Coq.State.t  (** (Full) State of node *)
    ; diags : Lang.Diagnostic.t list  (** Diagnostics associated to the node *)
    ; messages : Message.t list
    ; info : Info.t
    }

  val range : t -> Lang.Range.t
  val ast : t -> Ast.t option
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
    | FailedPermanent of Lang.Range.t
        (** Temporal Coq hack, avoids any computation *)

  val is_completed : t -> bool
end

(** Enviroment external to the document, this includes for now the [init] Coq
    state and the [workspace], which are used to build the first state of the
    document, usually by importing the prelude and other libs implicitly. *)
module Env : sig
  type t = private
    { init : Coq.State.t
    ; workspace : Coq.Workspace.t
    }

  val make : init:Coq.State.t -> workspace:Coq.Workspace.t -> t
end

(** A Flèche document is basically a [node list], which is a crude form of a
    meta-data map [Range.t -> data], where for now [data] is the contents of
    [Node.t]. *)
type t = private
  { uri : Lang.LUri.File.t  (** [uri] of the document *)
  ; version : int  (** [version] of the document *)
  ; contents : Contents.t  (** [contents] of the document *)
  ; nodes : Node.t list  (** List of document nodes *)
  ; completed : Completion.t
        (** Status of the document, usually either completed, suspended, or
            waiting for some IO / external event *)
  ; toc : Lang.Range.t CString.Map.t  (** table of contents *)
  ; env : Env.t  (** External document enviroment *)
  ; root : Coq.State.t
        (** [root] contains the first state document state, obtained by applying
            a workspace to Coq's initial state *)
  ; diags_dirty : bool  (** internal field *)
  }

(** Return the list of all asts in the doc *)
val asts : t -> Node.Ast.t list

(** Return the list of all diags in the doc *)
val diags : t -> Lang.Diagnostic.t list

(** Create a new Coq document, this is cached! Note that this operation always
    suceeds, but the document could be created in a `Failed` state if problems
    arise. *)
val create : env:Env.t -> uri:Lang.LUri.File.t -> version:int -> raw:string -> t

(** Update the contents of a document, updating the right structures for
    incremental checking. If the operation fails, the document will be left in
    `Failed` state. *)
val bump_version : version:int -> raw:string -> t -> t

(** Checking targets, this specifies what we expect check to reach *)
module Target : sig
  type t =
    | End
    | Position of int * int

  (** [reached ~range (line,col)] checks if [(line,col)] are before [range]'s
      end. *)
  val reached : range:Lang.Range.t -> int * int -> bool
end

(** [check ~io ~target ~doc ()], check document [doc], [target] will have Flèche
    stop after the point specified there has been reached. Output functions are
    in the [io] record, used to send partial updates. *)
val check : io:Io.CallBack.t -> target:Target.t -> doc:t -> unit -> t

(** [save ~doc] will save [doc] .vo file. It will fail if proofs are open, or if
    the document completion status is not [Yes] *)
val save : doc:t -> (unit, Loc.t) Coq.Protect.E.t

(** This is internal, to workaround the Coq multiple-docs problem *)
val create_failed_permanent :
  env:Env.t -> uri:Lang.LUri.File.t -> version:int -> raw:string -> t
