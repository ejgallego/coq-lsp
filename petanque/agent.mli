(* Petanque.Agent *)

module State : sig
  type t

  val hash : t -> int
  val equal : t -> t -> bool
  val goals : t -> string option
end

module Start_error : sig
  type t = string
end

(** [start uri thm] start a new proof for theorem [thm] in file [uri]. Note that
    uri is expected to be in the [file:///] format. *)
val start :
  uri:Lang.LUri.File.t -> thm:string -> (State.t, Start_error.t) Result.t

module Run_error : sig
  type t = string
end

(** [run_tac st tac] tries to run [tac] over state [st] *)
val run_tac : st:State.t -> tac:string -> (State.t, Run_error.t) Result.t
