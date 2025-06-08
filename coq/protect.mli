(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Rocq Effect Handling                   *)
(*************************************************************************)

(** This module reifies Coq side effects into an algebraic structure.

    This is very convenient for upper layer programming.

    As of today we handle feedback, exceptions, and interruptions. *)
module Error : sig
  type 'l t = private
    | User of 'l Message.Payload.t
    | Anomaly of 'l Message.Payload.t
end

(** This "monad" could be related to "Runners in action" (Ahman, Bauer), thanks
    to Guillaume Munch-Maccagnoni for the reference and for many useful tips! *)
module R : sig
  type ('a, 'l) t = private
    | Completed of ('a, 'l Error.t) result
    | Interrupted (* signal sent, eval didn't complete *)

  val error : Pp.t -> ('a, 'l) t
  val map : f:('a -> 'b) -> ('a, 'l) t -> ('b, 'l) t

  val map_error :
    f:('l Message.Payload.t -> 'm Message.Payload.t) -> ('a, 'l) t -> ('a, 'm) t

  (** Update the loc stored in the result, this is used by our cache-aware
      location *)
  val map_loc : f:('l -> 'm) -> ('a, 'l) t -> ('a, 'm) t
end

module E : sig
  type ('a, 'l) t = private
    { r : ('a, 'l) R.t
    ; feedback : 'l Message.t list
    }

  val map : f:('a -> 'b) -> ('a, 'l) t -> ('b, 'l) t
  val map_loc : f:('l -> 'm) -> ('a, 'l) t -> ('a, 'm) t
  val bind : f:('a -> ('b, 'l) t) -> ('a, 'l) t -> ('b, 'l) t
  val ok : 'a -> ('a, 'l) t
  val error : Pp.t -> ('a, 'l) t

  module O : sig
    val ( let+ ) : ('a, 'l) t -> ('a -> 'b) -> ('b, 'l) t
    val ( let* ) : ('a, 'l) t -> ('a -> ('b, 'l) t) -> ('b, 'l) t
  end
end

(** Must be hooked to allow [Protect] to capture the feedback. *)
val fb_queue : Loc.t Message.t list ref

(** Eval a function and reify the exceptions. Note [f] _must_ be pure, as in
    case of anomaly [f] may be re-executed with debug options. Beware, not
    thread-safe! [token] Does allow to interrupt the evaluation. *)
val eval : token:Limits.Token.t -> f:('i -> 'o) -> 'i -> ('o, Loc.t) E.t
