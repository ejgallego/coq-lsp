(** Messages from Coq *)
type 'l t =
  'l option * Lang.Diagnostic.Severity.t * 'l Lang.Qf.t list option * Pp.t

let map (loc, lvl, qf, msg) ~f =
  (Option.map f loc, lvl, Option.map (List.map (Lang.Qf.map f)) qf, msg)
