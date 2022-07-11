module Error = struct
  type t =
    | Eval of Loc.t option * Pp.t
    | Interrupted (* signal sent, eval didn't complete *)
end

let coq_protect ~f x =
  try
    let res = f x in
    Ok res
  with
  | Sys.Break -> Error Error.Interrupted
  | exn ->
    let e, info = Exninfo.capture exn in
    let loc = Loc.(get_loc info) in
    let msg = CErrors.iprint (e, info) in
    Error (Eval (loc, msg))
