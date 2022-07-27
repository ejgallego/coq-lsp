module Info = struct
  type 'a t =
    { res : 'a
    ; goal : Pp.t option
    ; feedback : Pp.t list
    }
end

let get_feedback fb_queue =
  let res = !fb_queue in
  fb_queue := [];
  res

let pr_goal (st : Coq_state.t) : Pp.t option =
  let st = Coq_state.to_coq st in
  Option.map
    (Vernacstate.LemmaStack.with_top ~f:(fun pstate ->
         let proof = Declare.Proof.get pstate in
         Printer.pr_open_subgoals ~quiet:false ~diffs:None proof))
    st.Vernacstate.lemmas

type 'a interp_result = 'a Info.t Coq_protect.R.t

let coq_interp ~st cmd =
  let st = Coq_state.to_coq st in
  let cmd = Coq_ast.to_coq cmd in
  Vernacinterp.interp ~st cmd |> Coq_state.of_coq

let interp ~st ~fb_queue cmd =
  Coq_protect.eval cmd ~f:(fun cmd ->
      let res = coq_interp ~st cmd in
      (* It is safe to call the printer here as the state is guaranteed to be
         the right one after `coq_interp`, but beware! *)
      let goal = pr_goal res in
      let feedback = List.rev @@ get_feedback fb_queue in
      { Info.res; goal; feedback })

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
    Coq_protect.R.Completed (Ok { Info.res; goal = None; feedback = [] })
  else
    let loc : Loc.t option = Marshal.from_channel ic in
    let msg : Pp.t = Marshal.from_channel ic in
    Coq_protect.R.Completed (Error (loc, msg))
