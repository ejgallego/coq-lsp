(** This modules reifies Coq side effects into an algebraic structure.

    This is obviously very convenient for upper layer programming.

    As of today this includes feedback and exceptions. *)
module Error : sig
  type 'l payload = 'l option * Pp.t

  type 'l t = private
    | User of 'l payload
    | Anomaly of 'l payload
end

module R : sig
  type ('a, 'l) t = private
    | Completed of ('a, 'l Error.t) result
    | Interrupted (* signal sent, eval didn't complete *)

  val error : Pp.t -> ('a, 'l) t
  val map : f:('a -> 'b) -> ('a, 'l) t -> ('b, 'l) t

  val map_error :
    f:('l Error.payload -> 'm Error.payload) -> ('a, 'l) t -> ('a, 'm) t

  (** Update the loc stored in the result, this is used by our cache-aware
      location *)
  val map_loc : f:('l -> 'm) -> ('a, 'l) t -> ('a, 'm) t
end

module E : sig
  type ('a, 'l) t =
    { r : ('a, 'l) R.t
    ; feedback : 'l Message.t list
    }

  val map : f:('a -> 'b) -> ('a, 'l) t -> ('b, 'l) t
  val map_loc : f:('l -> 'm) -> ('a, 'l) t -> ('a, 'm) t
  val bind : f:('a -> ('b, 'l) t) -> ('a, 'l) t -> ('b, 'l) t
  val ok : 'a -> ('a, 'l) t

  module O : sig
    val ( let+ ) : ('a, 'l) t -> ('a -> 'b) -> ('b, 'l) t
    val ( let* ) : ('a, 'l) t -> ('a -> ('b, 'l) t) -> ('b, 'l) t
  end
end

(** Must be hooked to allow [Protect] to capture the feedback. *)
val fb_queue : Loc.t Message.t list ref

(** Eval a function and reify the exceptions. Note [f] _must_ be pure, as in
    case of anomaly [f] may be re-executed with debug options. Beware, not
    thread-safe! *)
val eval : f:('i -> 'o) -> 'i -> ('o, Loc.t) E.t
