module InterpInfo : sig

  type t =
    { st : Vernacstate.t
    ; warnings : unit
    }

end

val interp_command :
  st:Vernacstate.t ->
  Vernacexpr.vernac_control ->
  (InterpInfo.t, Loc.t option * Pp.t) result

val mem_stats : unit -> int
