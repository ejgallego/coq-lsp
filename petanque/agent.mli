(************************************************************************)
(* Flèche => RL agent: petanque                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)

(** Petanque.Agent *)
module State : sig
  (** Full state of Coq *)
  type t

  val name : string

  (** OCaml poly Coq state hash; tuned for interactive edition. *)
  val hash : t -> int

  module Inspect : sig
    type t =
      | Physical  (** Flèche-based "almost physical" state eq *)
      | Goals
          (** Full goal equality; must faster than calling goals as it won't
              unelaborate them. Note that this may not fully capture proof state
              equality (it is possible to have similar goals but different
              evar_maps, but should be enough for all practical users. *)
  end

  (** [equal ?kind st1 st2] [kind] defaults to [Inspect.Physical] *)
  val equal : ?kind:Inspect.t -> t -> t -> bool

  module Proof : sig
    (** OCaml poly hash for Coq proof state. *)
    type t

    (** [equal ?kind st1 st2] [kind] defaults to [Inspect.Physical] *)
    val equal : ?kind:Inspect.t -> t -> t -> bool

    val hash : t -> int
  end

  val lemmas : t -> Proof.t option
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
    | No_state_at_point

  val to_string : t -> string
  val to_code : t -> int
  val coq : string -> t
  val system : string -> t
  val make_request : t -> t Request.Error.t
end

(** Petanque results *)
module R : sig
  type 'a t = ('a, Error.t) Request.R.t
end

module Run_opts : sig
  type t =
    { memo : bool [@default true]
    ; hash : bool [@default true]
    }
end

module Run_result : sig
  type 'a t =
    { st : 'a
    ; hash : int option [@default None]
          (** [State.Proof.hash st] if enabled / proof is open. *)
    ; proof_finished : bool
    ; feedback : (int * string) list  (** level and message *)
    }
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

(** [get_root_state ?opts ~doc] return the root state of the document [doc]. *)
val get_root_state :
  ?opts:Run_opts.t -> doc:Fleche.Doc.t -> unit -> State.t Run_result.t R.t

(** [get_state_at_pos ?opts ~doc ~position] return the state at position
    [position] in [doc]. Note that LSP positions are zero-based! *)
val get_state_at_pos :
     ?opts:Run_opts.t
  -> doc:Fleche.Doc.t
  -> point:int * int
  -> unit
  -> State.t Run_result.t R.t

(** [start ~token ~doc ~pre_commands ~thm] start a new proof for theorem [thm]
    in file [uri] under [fn]. [token] can be used to interrupt the computation.
    Returns the proof state or error otherwise. [pre_commands] is a string of
    dot-separated Coq commands that will be executed before the proof starts. *)
val start :
     token:Coq.Limits.Token.t
  -> doc:Fleche.Doc.t
  -> ?opts:Run_opts.t
  -> ?pre_commands:string
  -> thm:string
  -> unit
  -> State.t Run_result.t R.t

(** [run ~token ?memo ~st ~tac] tries to run [tac] over state [st]. [memo] (by
    default true) controls whether the command execution will be memoized in
    Flèche incremental engine. *)
val run :
     token:Coq.Limits.Token.t
  -> ?opts:Run_opts.t
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
