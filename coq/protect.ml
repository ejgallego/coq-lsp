module Error = struct
  type 'l payload = 'l option * Pp.t

  type 'l t =
    | User of 'l payload
    | Anomaly of 'l payload

  let map ~f = function
    | User e -> User (f e)
    | Anomaly e -> Anomaly (f e)
end

module R = struct
  type ('a, 'l) t =
    | Completed of ('a, 'l Error.t) result
    | Interrupted (* signal sent, eval didn't complete *)

  let error e = Completed (Error (Error.User (None, e)))

  let map ~f = function
    | Completed (Result.Ok r) -> Completed (Result.Ok (f r))
    | Completed (Result.Error r) -> Completed (Result.Error r)
    | Interrupted -> Interrupted

  let map_error ~f = function
    | Completed (Error e) -> Completed (Error (Error.map ~f e))
    | Completed (Ok r) -> Completed (Ok r)
    | Interrupted -> Interrupted

  let map_loc ~f =
    let f (loc, msg) = (Option.map f loc, msg) in
    map_error ~f
end

(* Eval and reify exceptions *)
let eval_exn ~f x =
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

module E = struct
  type ('a, 'l) t =
    { r : ('a, 'l) R.t
    ; feedback : 'l Message.t list
    }

  let map ~f { r; feedback } = { r = R.map ~f r; feedback }
  let map_message ~f (loc, lvl, msg) = (Option.map f loc, lvl, msg)

  let map_loc ~f { r; feedback } =
    { r = R.map_loc ~f r; feedback = List.map (map_message ~f) feedback }

  let ok v = { r = Completed (Ok v); feedback = [] }
end

let fb_queue : Loc.t Message.t list ref = ref []

(* Eval with reified exceptions and feedback *)
let eval ~f x =
  let r = eval_exn ~f x in
  let feedback = List.rev !fb_queue in
  let () = fb_queue := [] in
  { E.r; feedback }
