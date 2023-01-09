module Error = struct
  type payload = Loc.t option * Pp.t

  type t =
    | User of payload
    | Anomaly of payload

  let map ~f = function
    | User e -> User (f e)
    | Anomaly e -> Anomaly (f e)
end

module R = struct
  type 'a t =
    | Completed of ('a, Error.t) result
    | Interrupted (* signal sent, eval didn't complete *)

  let map ~f = function
    | Completed (Result.Ok r) -> Completed (Result.Ok (f r))
    | Completed (Result.Error r) -> Completed (Result.Error r)
    | Interrupted -> Interrupted

  let map_error ~f = function
    | Completed (Error e) -> Completed (Error (Error.map ~f e))
    | res -> res

  let map_loc ~f =
    let f (loc, msg) = (Option.map f loc, msg) in
    map_error ~f
end

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
    if CErrors.is_anomaly e then R.Completed (Error (Anomaly (loc, msg)))
    else R.Completed (Error (User (loc, msg)))
