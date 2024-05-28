(************************************************************************)
(* Flèche => RL agent: petanque                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)

(** Petanque.Agent *)

module State : sig
  type t

  val hash : t -> int
  val equal : t -> t -> bool
end

module Env : sig
  (** Coq Workspaces / project enviroments *)
  type t
end

(** Petanque errors *)
module Error : sig
  type t =
    | Interrupted
    | Parsing of string
    | Coq of string
    | Anomaly of string
    | Theorem_not_found of string

  val to_string : t -> string
  val to_code : t -> int
end

(** Petanque results *)
module R : sig
  type 'a t = ('a, Error.t) Result.t
end

(** I/O handling, by default, print to stderr *)

(** [trace header extra message] *)
val trace_ref : (string -> ?extra:string -> string -> unit) ref

(** [message level message] *)
val message_ref : (lvl:Fleche.Io.Level.t -> message:string -> unit) ref

(** [init ~debug ~root] Initializes Coq, with project and workspace settings
    from [root]. [root] needs to be in URI format. This function needs to be
    called _once_ before all others. *)
val init :
  token:Coq.Limits.Token.t -> debug:bool -> root:Lang.LUri.File.t -> Env.t R.t

(** [start uri thm] start a new proof for theorem [thm] in file [uri]. *)
val start :
     token:Coq.Limits.Token.t
  -> env:Env.t
  -> uri:Lang.LUri.File.t
  -> thm:string
  -> State.t R.t

(** [run_tac ~token ~st ~tac] tries to run [tac] over state [st] *)
val run_tac :
  token:Coq.Limits.Token.t -> st:State.t -> tac:string -> State.t R.t

(** [goals ~token ~st] return the list of goals for a given [st] *)
val goals :
     token:Coq.Limits.Token.t
  -> st:State.t
  -> string Coq.Goals.reified_pp option R.t

(** Return the list of defined constants and inductives for a given state. For
    now we just return their fully qualified name, but more options are of
    course possible. *)
val premises : token:Coq.Limits.Token.t -> st:State.t -> string list R.t
