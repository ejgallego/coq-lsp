let pr_letype_env ~goal_concl_style env sigma x =
  Printer.pr_letype_env ~goal_concl_style env sigma x

let pr_letype_env ~token ~goal_concl_style env sigma x =
  let f = pr_letype_env ~goal_concl_style env sigma in
  Protect.eval ~token ~f x

let pr_goals ~token ~proof =
  let proof =
    State.Proof.to_coq proof |> Vernacstate.LemmaStack.get_top
    |> Declare.Proof.get
  in
  let f = Printer.pr_open_subgoals in
  Protect.eval ~token ~f proof
