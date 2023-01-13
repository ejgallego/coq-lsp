(** time-based stats *)
module Kind : sig
  type t =
    | Hashing
    | Parsing
    | Exec
end

val get : kind:Kind.t -> float
val record : kind:Kind.t -> f:('a -> 'b) -> 'a -> 'b * float
val reset : unit -> unit

type t

val zero : unit -> t
val to_string : t -> string
val dump : unit -> t
val restore : t -> unit
val get_f : t -> kind:Kind.t -> float

(** Pretty-print memory info as words *)
val pp_words : Format.formatter -> float -> unit
