module State : Internal.Conv with type Internal.coq = Vernacstate.Parser.t

module Parsable : sig
  type t

  val make : ?loc:Loc.t -> char Gramlib.Stream.t -> t
end

module Proof_mode : Internal.Conv with type Internal.coq = Pvernac.proof_mode

(** The main entry: reads an vernac command or a tactic (depending on the proof
    mode) *)
val parse : State.t -> Proof_mode.t option -> Parsable.t -> Ast.t option

val discard_to_dot : Parsable.t -> unit
