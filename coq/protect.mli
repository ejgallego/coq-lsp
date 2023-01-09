module Error : sig
  type payload = Loc.t option * Pp.t

  type t = private
    | User of payload
    | Anomaly of payload
end

module R : sig
  type 'a t = private
    | Completed of ('a, Error.t) result
    | Interrupted (* signal sent, eval didn't complete *)

  val map : f:('a -> 'b) -> 'a t -> 'b t
  val map_error : f:(Error.payload -> Error.payload) -> 'a t -> 'a t

  (** Update the loc stored in the result, this is used by our cache-aware
      location *)
  val map_loc : f:(Loc.t -> Loc.t) -> 'a t -> 'a t
end

(** Eval a function and reify the exceptions. Note [f] _must_ be pure, as in
    case of anomaly [f] may be re-executed with debug options. *)
val eval : f:('i -> 'o) -> 'i -> 'o R.t
