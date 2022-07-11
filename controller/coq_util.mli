module Error : sig
  type t =
    | Eval of Loc.t option * Pp.t
    | Interrupted (* signal sent, eval didn't complete *)
end

val coq_protect : f:('a -> 'b) -> 'a -> ('b, Error.t) result
