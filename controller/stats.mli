module Kind : sig
  type t = Hashing | Parsing | Exec
end

val record : kind:Kind.t -> f:('a -> 'b) -> 'a -> 'b

val dump : unit -> string

val reset : unit -> unit
