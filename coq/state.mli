type t

val marshal_in : in_channel -> t
val marshal_out : out_channel -> t -> unit
val of_coq : Vernacstate.t -> t
val to_coq : t -> Vernacstate.t
val compare : t -> t -> int
val equal : t -> t -> bool
val hash : t -> int
val mode : st:t -> Pvernac.proof_mode option
val parsing : st:t -> Vernacstate.Parser.t
val lemmas : st:t -> Vernacstate.LemmaStack.t option

(** Execute a command in state [st]. Unfortunately this can produce anomalies as
    Coq state setting is imperative, so we need to wrap it in protect. *)
val in_state : st:t -> f:('a -> 'b) -> 'a -> 'b Protect.E.t

(** Drop the proofs from the state *)
val drop_proofs : st:t -> t

(** Admit an ongoing proof *)
val admit : st:t -> t
