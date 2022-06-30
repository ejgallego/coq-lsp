val interp_command :
  st:Vernacstate.t ->
  Vernacexpr.vernac_control ->
  (Vernacstate.t, Loc.t option * Pp.t) result

val mem_stats : unit -> int
