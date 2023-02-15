module Stats : sig
  type 'a t =
    { res : 'a
    ; cache_hit : bool
    ; memory : int
    ; time : float
    }
end

(** Interpret a command, possibly memoizing it *)
val interp_command :
  st:Coq.State.t -> Coq.Ast.t -> Coq.State.t Coq.Interp.interp_result Stats.t

val interp_admitted : st:Coq.State.t -> (Coq.State.t, Loc.t) Coq.Protect.E.t

(** Stats *)
val mem_stats : unit -> int

module CacheStats : sig
  val reset : unit -> unit
  val stats : unit -> string
end

(** Not working yet *)
val load_from_disk : file:string -> unit

val save_to_disk : file:string -> unit

(** debug *)
val input_info : Coq.Ast.t * Coq.State.t -> string
