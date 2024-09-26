val pr_letype_env :
     token:Limits.Token.t
  -> goal_concl_style:bool
  -> Environ.env
  -> Evd.evar_map
  -> EConstr.t
  -> (Pp.t, Loc.t) Protect.E.t

val pr_goals :
  token:Limits.Token.t -> proof:State.Proof.t -> (Pp.t, Loc.t) Protect.E.t
