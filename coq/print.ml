let pr_letype_env ~goal_concl_style env sigma x =
  Printer.pr_letype_env ~goal_concl_style env sigma x

let pr_letype_env ~goal_concl_style env sigma x =
  let f = pr_letype_env ~goal_concl_style env sigma in
  Protect.eval ~pure:true ~f x
