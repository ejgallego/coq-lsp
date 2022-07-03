module InterpInfo : sig

  type t =
    { st : Vernacstate.t
    ; warnings : unit
    }

end

module Stats : sig

  type 'a t = { res : 'a; cache_hit : bool; memory : int; time: float }

end

(* debug *)
val input_info : (Vernacexpr.vernac_control * Vernacstate.t) -> string

val interp_command :
  st:Vernacstate.t ->
  Vernacexpr.vernac_control ->
  (InterpInfo.t, Loc.t option * Pp.t) result Stats.t

val mem_stats : unit -> int

val load_from_disk : file:string -> unit
val save_to_disk : file:string -> unit
