module Info = struct
  type 'a t =
    { res : 'a
    ; warnings : unit
    }
end

type 'a interp_result = 'a Info.t Coq_protect.R.t

let coq_interp ~st cmd =
  let st = Coq_state.to_coq st in
  let cmd = Coq_ast.to_coq cmd in
  Vernacinterp.interp ~st cmd |> Coq_state.of_coq

let interp ~st cmd =
  Coq_protect.eval cmd ~f:(fun cmd ->
      let res = coq_interp ~st cmd in
      { Info.res; warnings = () })

let marshal_out f oc res =
  match res with
  | Coq_protect.R.Interrupted -> ()
  | Coq_protect.R.Completed res -> (
    match res with
    | Ok res ->
      Marshal.to_channel oc 0 [];
      f oc res.Info.res
    | Error (loc, msg) ->
      Marshal.to_channel oc 1 [];
      Marshal.to_channel oc loc [];
      Marshal.to_channel oc msg [];
      ())

let marshal_in f ic =
  let tag : int = Marshal.from_channel ic in
  if tag = 0 then
    let res = f ic in
    Coq_protect.R.Completed (Ok { Info.res; warnings = () })
  else
    let loc : Loc.t option = Marshal.from_channel ic in
    let msg : Pp.t = Marshal.from_channel ic in
    Coq_protect.R.Completed (Error (loc, msg))
