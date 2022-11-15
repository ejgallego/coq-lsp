type error = Loc.t option * Pp.t

module R = struct
  type 'a t =
    | Completed of ('a, Loc.t option * Pp.t) result
    | Interrupted (* signal sent, eval didn't complete *)
end

let map_loc ~f = function
  | R.Completed (Error (loc, msg)) ->
    R.Completed (Error (Option.map f loc, msg))
  | res -> res

let eval ~f x =
  try
    let res = f x in
    R.Completed (Ok res)
  with
  | Sys.Break -> R.Interrupted
  | exn ->
    let e, info = Exninfo.capture exn in
    let loc = Loc.(get_loc info) in
    let msg = CErrors.iprint (e, info) in
    R.Completed (Error (loc, msg))
