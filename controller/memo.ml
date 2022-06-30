module InterpInfo = struct

  type t =
    { st : Vernacstate.t
    ; warnings : unit
    }

end

type interp_result = (InterpInfo.t, Loc.t option * Pp.t) result

let coq_interp ~st cmd =
  let st = Vernacinterp.interp ~st cmd in
  { InterpInfo.st; warnings = () }

let cache : (Vernacstate.t * Vernacexpr.vernac_control, interp_result) Hashtbl.t = Hashtbl.create 1000

let in_cache st stm =
  let kind = Stats.Kind.Hashing in
  Stats.record ~kind ~f:(Hashtbl.find_opt) cache (st, stm)

let interp_command ~st stm : _ result =
  match in_cache st stm with
  | Some st ->
    Lsp.Io.log_error "coq" "cache hit";
    st
  | None ->
    Lsp.Io.log_error "coq" "cache miss";
    let kind = Stats.Kind.Exec in
    let res =
      Stats.record ~kind
        ~f:(Coq_util.coq_protect (coq_interp ~st)) stm
    in
    let () = Hashtbl.add cache (st,stm) res in
    res

let mem_stats () = Obj.reachable_words (Obj.magic cache)
