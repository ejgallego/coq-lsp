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
  val name : unit -> string
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

  let name () = "Control.interrupt"
  let available = true
end

module Mp = Limits_mp_impl

type backend =
  | Coq
  | Mp

let backend : (module Intf) ref = ref (module Coq : Intf)

let select = function
  | Coq -> backend := (module Coq)
  | Mp -> backend := (module Mp)

(* Set this to false for 8.19 and lower *)
let select_best = function
  | None ->
    if Mp.available && Version.safe_for_memprof then select Mp else select Coq
  | Some backend -> select backend

module Token = struct
  type t =
    | C of Coq.Token.t
    | M of Mp.Token.t
    | A (* Atomic operation *)

  let create () =
    let module M = (val !backend) in
    match M.name () with
    | "memprof-limits" -> M (Mp.Token.create ())
    | "Control.interrupt" | _ -> C (Coq.Token.create ())

  let set = function
    | C token -> Coq.Token.set token
    | M token -> Mp.Token.set token
    | A -> ()

  let is_set = function
    | C token -> Coq.Token.is_set token
    | M token -> Mp.Token.is_set token
    | A -> false
end

let create_atomic () = Token.A

let start () =
  let module M = (val !backend) in
  M.start ()

let limit ~token ~f x =
  let module M = (val !backend) in
  match token with
  | Token.C token -> Coq.limit ~token ~f x
  | Token.M token -> Mp.limit ~token ~f x
  | Token.A ->
    let () = Control.interrupt := false in
    Ok (f x)

let name () =
  let module M = (val !backend) in
  M.name ()

let available = true
