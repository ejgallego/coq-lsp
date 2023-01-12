let pr_ltype_env ~goal_concl_style env sigma x =
  Printer.pr_ltype_env ~goal_concl_style env sigma x

let pr_ltype_env ~goal_concl_style env sigma x =
  let f = pr_ltype_env ~goal_concl_style env sigma in
  Protect.eval ~f x
