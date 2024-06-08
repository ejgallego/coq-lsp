(************************************************************************)
(* Flèche => RL agent: petanque                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)

(** Petanque.Agent *)

module State : sig
  type t

  val name : string
  val hash : t -> int
  val equal : t -> t -> bool
end

module Env : sig
  (** Coq Workspaces / project enviroments *)
  type t = Fleche.Doc.Env.t

  val name : string
end

(** Petanque errors *)
module Error : sig
  type t =
    | Interrupted
    | Parsing of string
    | Coq of string
    | Anomaly of string
    | System of string
    | Theorem_not_found of string

  val to_string : t -> string
  val to_code : t -> int
end

(** Petanque results *)
module R : sig
  type 'a t = ('a, Error.t) Result.t
end

module Run_result : sig
  type 'a t =
    | Proof_finished of 'a
    | Current_state of 'a
end

(** I/O handling, by default, print to stderr *)

(** [trace header extra message] *)
val trace_ref : (string -> ?extra:string -> string -> unit) ref

(** [message level message] *)
val message_ref : (lvl:Fleche.Io.Level.t -> message:string -> unit) ref

(** To be called by the shell *)
val init_agent : debug:bool -> unit

(** [set_workspace ~root] Sets project and workspace settings from [root].
    [root] needs to be in URI format. If called repeteadly, overrides the
    previous call. *)
val set_workspace :
  token:Coq.Limits.Token.t -> debug:bool -> root:Lang.LUri.File.t -> Env.t R.t

(** [start ~token ~fn ~uri ~pre_commands ~thm] start a new proof for theorem
    [thm] in file [uri] under [fn]. [token] can be used to interrupt the
    computation. Returns the proof state or error otherwise. [pre_commands] is a
    string of dot-separated Coq commands that will be executed before the proof
    starts. *)
val start :
     token:Coq.Limits.Token.t
  -> fn:(io:Fleche.Io.CallBack.t -> Lang.LUri.File.t -> Fleche.Doc.t R.t)
  -> uri:Lang.LUri.File.t
  -> ?pre_commands:string
  -> thm:string
  -> unit
  -> State.t R.t

(** [run_tac ~token ~st ~tac] tries to run [tac] over state [st] *)
val run_tac :
     token:Coq.Limits.Token.t
  -> st:State.t
  -> tac:string
  -> State.t Run_result.t R.t

(** [goals ~token ~st] return the list of goals for a given [st] *)
val goals :
     token:Coq.Limits.Token.t
  -> st:State.t
  -> string Coq.Goals.reified_pp option R.t

module Premise : sig
  type t =
    { full_name : string
          (* should be a Coq DirPath, but let's go step by step *)
    ; file : string (* file (in FS format) where the premise is found *)
    ; kind : (string, string) Result.t (* type of object *)
    ; range : (Lang.Range.t, string) Result.t (* a range if known *)
    ; offset : (int * int, string) Result.t
          (* a offset in the file if known (from .glob files) *)
    ; raw_text : (string, string) Result.t (* raw text of the premise *)
    }
end

(** Return the list of defined constants and inductives for a given state. For
    now we just return their fully qualified name, but more options are of
    course possible. *)
val premises : token:Coq.Limits.Token.t -> st:State.t -> Premise.t list R.t
