(* We'd like to move this code to Lang, but it is still too specific *)
module Token = Memprof_limits.Token

(* overclock-mode *)
let oc_mode = false

let oc_init () =
  let sampling_rate = 1e-2 in
  let callstack_size = 0 in
  let tracker = Memprof_limits.Memprof.null_tracker in
  Memprof_limits.Memprof.start ~sampling_rate ~callstack_size tracker

let start () =
  if oc_mode then oc_init ();
  Memprof_limits.start_memprof_limits ();
  Memprof_limits.set_global_memory_limit 8000000 (* 8 GiB *)

exception Allocations_exceeded of Int64.t

let allocation_limit = Memprof_limits.max_allocation_limit
(* let allocation_limit = Int64.of_int 1000000000000 *)

let limit ~token ~f x =
  let f () = f x in
  let limit = allocation_limit in
  let f () = Memprof_limits.limit_allocations ~limit f in
  let f () = Memprof_limits.limit_global_memory f in
  let f () = Memprof_limits.limit_with_token ~token f in
  match f () with
  | Ok (Ok (Ok (res, _amount))) -> Ok res
  | Ok (Ok (Error err)) -> Error err
  | Ok (Error err) -> Error err
  | Error err -> Error err

let name () = "memprof-limits"
let available = true
