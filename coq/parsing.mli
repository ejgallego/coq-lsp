module Parsable : sig
  type t

  val make : ?loc:Loc.t -> (unit, char) Gramlib.Stream.t -> t
  val loc : t -> Loc.t
end

val parse :
     token:Limits.Token.t
  -> st:State.t
  -> Parsable.t
  -> (Ast.t option, Loc.t) Protect.E.t

val discard_to_dot : Parsable.t -> unit
