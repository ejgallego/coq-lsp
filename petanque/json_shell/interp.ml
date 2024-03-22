open Protocol
module A = Petanque.Agent

let interp (c : Command.t) : Answer.t =
  match c with
  | Start { uri; thm } ->
    let uri =
      Lang.LUri.of_string uri |> Lang.LUri.File.of_uri |> Result.get_ok
    in
    let st = A.start ~uri ~thm in
    Answer.Start st
  | Run_tac { st; tac } ->
    let st = A.run_tac ~st ~tac in
    Answer.Run_tac st
  | Goals { st } ->
    let goals = A.State.goals st in
    let error = "no goals at this state" in
    Answer.Goals (Base.Result.of_option ~error goals)
