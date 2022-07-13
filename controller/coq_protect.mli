module R : sig
  type 'a t =
    | Completed of ('a, Loc.t option * Pp.t) result
    | Interrupted (* signal sent, eval didn't complete *)
end

val eval : f:('i -> 'o) -> 'i -> 'o R.t
