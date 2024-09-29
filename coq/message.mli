(** Messages from Coq *)
type 'l t =
  'l option * Lang.Diagnostic.Severity.t * 'l Lang.Qf.t list option * Pp.t
(* Note, must be keep in sync with Protect.Error.payload, until we refactor
   stuff *)

val map : 'l t -> f:('l -> 'm) -> 'm t
