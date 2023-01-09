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
let rec eval_exn ~f ~retry x =
  try
    let res = f x in
    R.Completed (Ok res)
  with
  | Sys.Break -> R.Interrupted
  | exn -> (
    let exn, info = Exninfo.capture exn in
    let loc = Loc.(get_loc info) in
    let msg = CErrors.iprint (exn, info) in
    let anomaly = CErrors.is_anomaly exn in
    let bt = Printexc.backtrace_status () in
    match (anomaly, bt, retry) with
    | true, true, _ | true, false, false ->
      R.Completed (Error (Anomaly (loc, msg)))
    | true, false, true ->
      (* This doesn't work because the state unfreeze will restore the
         "no-backtrace" status *)
      CDebug.set_flags "backtrace";
      let res = eval_exn ~f ~retry:false x in
      CDebug.set_flags "-backtrace";
      res
    | false, _, _ -> R.Completed (Error (User (loc, msg))))

module E = struct
  type ('a, 'l) t =
    { r : ('a, 'l) R.t
    ; feedback : 'l Message.t list
    }

  let map ~f { r; feedback } = { r = R.map ~f r; feedback }
  let map_message ~f (loc, lvl, msg) = (Option.map f loc, lvl, msg)

  let map_loc ~f { r; feedback } =
    { r = R.map_loc ~f r; feedback = List.map (map_message ~f) feedback }
end

let fb_queue : Loc.t Message.t list ref = ref []

(* Eval with reified exceptions and feedback *)
let eval ~f ~pure x =
  let r = eval_exn ~retry:pure ~f x in
  let feedback = List.rev !fb_queue in
  let () = fb_queue := [] in
  { E.r; feedback }
