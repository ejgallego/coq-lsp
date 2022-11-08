type error = Loc.t option * Pp.t

module R : sig
  type 'a t =
    | Completed of ('a, error) result
    | Interrupted (* signal sent, eval didn't complete *)
end

val eval : f:('i -> 'o) -> 'i -> 'o R.t

(** Update the loc stored in the result, this is used by our cache-aware
    location *)
val map_loc : f:(Loc.t -> Loc.t) -> 'a R.t -> 'a R.t
