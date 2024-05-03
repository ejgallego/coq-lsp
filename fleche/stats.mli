(** time and memory-based stats *)
module Kind : sig
  type t =
    | Hashing
    | Parsing
    | Exec
end

type t =
  { time : float
  ; memory : float
  }

(** [record ~kind ~f x] returns [f x] with timing and memory use data attached
    to it; it will also update the global table for [kind] *)
val record : kind:Kind.t -> f:('a -> 'b) -> 'a -> 'b * t

(** [get_accumulated ~kind] returns global accumulated stats for [kind] *)
val get_accumulated : kind:Kind.t -> t

(** [reset ()] Reset global accumulated stats *)
val reset : unit -> unit

module Global : sig
  (** Operations to save/restore global accumulated state *)
  type nonrec 'a stats = t

  type t

  val zero : unit -> t
  val dump : unit -> t
  val restore : t -> unit

  (** Get a particular field *)
  val get_f : t -> kind:Kind.t -> unit stats

  val to_string : t -> string
end

(** Pretty-print memory info as words *)
val pp_words : Format.formatter -> float -> unit
