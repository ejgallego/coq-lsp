(* We'd like to move this code to Lang, but it is still too specific *)
module Token = struct
  type t = unit

  let create () = ()
  let set () = ()
  let is_set () = false
end

let start () = ()
let limit ~token:_ ~f x = Result.Ok (f x)
let name () = "memprof-limits (fake)"
let available = false
