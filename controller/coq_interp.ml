module Info = struct

  type 'a t =
    { res : 'a
    ; warnings : unit
    }

end

type 'a interp_result = ('a Info.t, Loc.t option * Pp.t) result

let interp ~st cmd =
  Coq_util.coq_protect cmd
    ~f:(fun cmd ->
        let res = Vernacinterp.interp ~st (Coq_ast.to_coq cmd) in
        { Info.res; warnings = () })

