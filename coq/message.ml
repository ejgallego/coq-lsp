(** Messages from Coq *)
type t = Loc.t option * int * Pp.t

type coq = Feedback.feedback
