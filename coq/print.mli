val pr_letype_env :
     goal_concl_style:bool
  -> Environ.env
  -> Evd.evar_map
  -> EConstr.t
  -> (Pp.t, Loc.t) Protect.E.t
