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

(** Protocol notes:

    The idea is that the types of the functions here have a direct translation
    to the JSON-RPC (or any other) protocol.

    Thus, types here correspond to types in the wire, except for cases where the
    protocol layer performs an implicit mapping on types.

    So far, the mappings are:

    - [uri] <-> [Doc.t]
    - [int] <-> [State.t]

    The [State.t] mapping is easy to do at the protocol level with a simple
    mapping, however [uri -> Doc.t] may need to yield to the document manager to
    build the corresponding [doc]. This is very convenient for users, but
    introduces a little bit more machinery.

    We could imagine a future where [State.t] need to be managed asynchronously,
    then the same approach that we use for [Doc.t] could happen. *)

(** [start ~token ~doc ~pre_commands ~thm] start a new proof for theorem [thm]
    in file [uri] under [fn]. [token] can be used to interrupt the computation.
    Returns the proof state or error otherwise. [pre_commands] is a string of
    dot-separated Coq commands that will be executed before the proof starts. *)
val start :
     token:Coq.Limits.Token.t
  -> doc:Fleche.Doc.t
  -> ?pre_commands:string
  -> thm:string
  -> unit
  -> State.t R.t

(** [run ~token ?memo ~st ~tac] tries to run [tac] over state [st]. [memo] (by
    default true) controls whether the command execution will be memoized in
    Flèche incremental engine. *)
val run :
     token:Coq.Limits.Token.t
  -> ?memo:bool
  -> st:State.t
  -> tac:string
  -> unit
  -> State.t Run_result.t R.t

(** [goals ~token ~st] return the list of goals for a given [st] *)
val goals :
     token:Coq.Limits.Token.t
  -> st:State.t
  -> string Coq.Goals.reified_pp option R.t

module Premise : sig
  module Info : sig
    (* (from .glob files) *)
    type t =
      { kind : string (* type of object *)
      ; range : Lang.Range.t option (* a range *)
      ; offset : int * int (* a offset in the file *)
      ; raw_text : (string, string) Result.t (* raw text of the premise *)
      }
  end

  type t =
    { full_name : string
          (* should be a Coq DirPath, but let's go step by step *)
    ; file : string (* file (in FS format) where the premise is found *)
    ; info : (Info.t, string) Result.t (* Info about the object, if available *)
    }
end

(** Return the list of defined constants and inductives for a given state. For
    now we just return their fully qualified name, but more options are of
    course possible. *)
val premises : token:Coq.Limits.Token.t -> st:State.t -> Premise.t list R.t
