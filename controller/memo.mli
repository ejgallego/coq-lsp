module Stats : sig
  type 'a t =
    { res : 'a
    ; cache_hit : bool
    ; memory : int
    ; time : float
    }
end

(* debug *)
val input_info : Coq_ast.t * Coq_state.t -> string

val interp_command :
     st:Coq_state.t
  -> fb_queue:Pp.t Loc.located list ref
  -> Coq_ast.t
  -> Coq_state.t Coq_interp.interp_result Stats.t

val mem_stats : unit -> int
val load_from_disk : file:string -> unit
val save_to_disk : file:string -> unit

module CacheStats : sig
  val reset : unit -> unit
  val stats : unit -> string
end
