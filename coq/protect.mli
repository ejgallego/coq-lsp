module Error : sig
  type t = Loc.t option * Pp.t
end

module R : sig
  type 'a t =
    | Completed of ('a, Error.t) result
    | Interrupted (* signal sent, eval didn't complete *)

  val map : f:('a -> 'b) -> 'a t -> 'b t
  val map_error : f:(Error.t -> Error.t) -> 'a t -> 'a t

  (** Update the loc stored in the result, this is used by our cache-aware
      location *)
  val map_loc : f:(Loc.t -> Loc.t) -> 'a t -> 'a t
end

(** Eval a function and reify the exceptions. Note [f] _must_ be pure, as in
    case of anomaly [f] may be re-executed with debug options. *)
val eval : f:('i -> 'o) -> 'i -> 'o R.t
