(** time-based stats *)
module Kind : sig
  type t =
    | Hashing
    | Parsing
    | Exec
end

val get : kind:Kind.t -> float
val record : kind:Kind.t -> f:('a -> 'b) -> 'a -> 'b * float
val to_string : unit -> string
val reset : unit -> unit

type t

val dump : unit -> t
val restore : t -> unit
val get_f : t -> kind:Kind.t -> float
