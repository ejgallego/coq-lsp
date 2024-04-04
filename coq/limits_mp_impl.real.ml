(* We'd like to move this code to Lang, but it is still too specific *)
module Token = Memprof_limits.Token

let start () = Memprof_limits.start_memprof_limits ()

let limit ~token ~f x =
  let f () = f x in
  Memprof_limits.limit_with_token ~token f

let name = "memprof-limits"
let available = true
