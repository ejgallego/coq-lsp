module Parsable : sig
  type t

  val make : ?loc:Loc.t -> char Gramlib.Stream.t -> t
  val loc : t -> Loc.t
end

val parse : st:State.t -> Parsable.t -> Ast.t option Protect.E.t
val discard_to_dot : Parsable.t -> unit
