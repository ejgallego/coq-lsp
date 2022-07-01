module CS = Stats

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

module Stats = struct

  type 'a t = { res : 'a; cache_hit : bool; memory : int; time: float }

  let make ?(cache_hit=false) res = { res; cache_hit; memory = 0; time = 0.0 }

end

let cache : (Vernacstate.t * Vernacexpr.vernac_control, interp_result) Hashtbl.t ref = ref (Hashtbl.create 1000)

let in_cache st stm =
  let kind = CS.Kind.Hashing in
  CS.record ~kind ~f:(Hashtbl.find_opt) !cache (st, stm)

let interp_command ~st stm : _ result Stats.t =
  match in_cache st stm with
  | Some st ->
    Lsp.Io.log_error "coq" "cache hit";
    Stats.make ~cache_hit:true st
  | None ->
    Lsp.Io.log_error "coq" "cache miss";
    let kind = CS.Kind.Exec in
    let res =
      CS.record ~kind
        ~f:(Coq_util.coq_protect (coq_interp ~st)) stm
    in
    let () = Hashtbl.add !cache (st,stm) res in
    Stats.make res

let mem_stats () = Obj.reachable_words (Obj.magic cache)

let load_from_disk ~file =
  let in_c = open_in_bin file in
  cache := Marshal.from_channel in_c;
  close_in in_c

let save_to_disk ~file =
  let out_c = open_out_bin file in
  Marshal.to_channel out_c !cache [];
  close_out out_c
