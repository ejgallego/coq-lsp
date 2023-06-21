(* We'd like to move this code to Lang, but it is still too specific *)

module type Intf = sig

  module Token : sig
    type t

    val create : unit -> t
    val set : t -> unit
    val is_set : t -> bool
  end

  val start : unit -> unit
  val limit : token: Token.t -> f:('a -> 'b) -> 'a -> ('b, exn) Result.t

end

module Memprof : Intf = struct

  module Token = Memprof_limits.Token

  let start () = Memprof_limits.start_memprof_limits ()

  let limit ~token ~f x =
    let f () = f x in
    Memprof_limits.limit_with_token ~token f
end

module CoqPolling : Intf = struct
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
end

include Memprof
