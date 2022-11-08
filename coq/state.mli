type t

val compare : t -> t -> int
val mode : st:t -> Parse.Proof_mode.t option
val parsing : st:t -> Parse.State.t
val in_state : st:t -> f:('a -> 'b) -> 'a -> 'b

module Proof : sig
  type proof = Vernacstate.LemmaStack.t

  val get : st:t -> proof option
end

(* Error recovery *)
val drop_proofs : st:t -> t

module Marshal : sig
  val read : in_channel -> t
  val write : out_channel -> t -> unit
end

module Internal : sig
  val of_coq : Vernacstate.t -> t
  val to_coq : t -> Vernacstate.t
end
