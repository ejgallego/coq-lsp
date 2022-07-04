module Kind : sig
  type t = Hashing | Parsing | Exec
end

val get : kind:Kind.t -> float
val record : kind:Kind.t -> f:('a -> 'b) -> 'a -> 'b * float

val dump : unit -> string

val reset : unit -> unit
