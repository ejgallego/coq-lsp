(* This is a wrapper for the memprof-limits lib, as it is not
   available in most setups *)
module Token : sig
  type t
  val create : unit -> t
  val set : t -> unit
  val is_set : t -> bool
end

val start : unit -> unit

val limit_with_token : token:Token.t -> (unit -> 'a) -> ('a, exn) Result.t
