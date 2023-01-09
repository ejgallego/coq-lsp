let pr_ltype_env ~goal_concl_style env sigma x =
  Printer.pr_ltype_env ~goal_concl_style env sigma x

let pr_ltype_env ~goal_concl_style env sigma x =
  let f = pr_ltype_env ~goal_concl_style env sigma in
  match Protect.eval ~f x with
  | Protect.R.Completed (Ok pr) -> pr
  | _ -> Pp.str "printer failed!"
