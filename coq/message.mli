(** Messages from Coq *)
type 'l t = 'l option * Lang.Diagnostic.Severity.t * Pp.t
