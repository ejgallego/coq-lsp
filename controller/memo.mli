module Stats : sig

  type 'a t = { res : 'a; cache_hit : bool; memory : int; time: float }

end

(* debug *)
val input_info : (Coq_ast.t * Vernacstate.t) -> string

val interp_command :
  st:Vernacstate.t ->
  Coq_ast.t ->
  Vernacstate.t Coq_interp.interp_result Stats.t

val mem_stats : unit -> int

val load_from_disk : file:string -> unit
val save_to_disk : file:string -> unit
