(* This is a wrapper for memprof-limits libs *)
module type Intf = sig
  module Token : sig
    type t

    val create : unit -> t
    val set : t -> unit
    val is_set : t -> bool
  end

  val start : unit -> unit
  val limit : token:Token.t -> f:('a -> 'b) -> 'a -> ('b, exn) Result.t
  val name : string
  val available : bool
end

module Coq : Intf
module Mp : Intf
include Intf

type backend =
  | Coq
  | Mp

(** *Must* be called *only* once *)
val select : backend -> unit

val create_atomic : unit -> Token.t
