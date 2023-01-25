(** Messages from Coq *)
type 'l t = 'l option * int * Pp.t

type coq = Feedback.feedback
