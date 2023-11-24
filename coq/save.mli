val save_vo :
     st:State.t
  -> ldir:Names.DirPath.t
  -> in_file:string
  -> (unit, Loc.t) Protect.E.t
