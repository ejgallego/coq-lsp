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

module Coq : Intf = struct
  module Token : sig
    type t

    val create : unit -> t
    val set : t -> unit
    val is_set : t -> bool
  end = struct
    type t = bool ref

    let create () = ref false

    let set t =
      t := true;
      Control.interrupt := true

    let is_set t = !t
  end

  let start () = ()

  let limit ~token ~f x =
    if Token.is_set token then Error Sys.Break
    else
      let () = Control.interrupt := false in
      try Ok (f x) with Sys.Break -> Error Sys.Break

  let name = "Control.interrupt"
  let available = true
end

module Mp = Limits_mp_impl
include Coq
