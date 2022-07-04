module Info : sig

  type 'a t =
    { res : 'a
    ; warnings : unit
    }

end

type 'a interp_result = ('a Info.t, Loc.t option * Pp.t) result

val interp : st:Vernacstate.t -> Vernacexpr.vernac_control -> Vernacstate.t interp_result
