module CS = Stats

module Stats = struct

  type 'a t = { res : 'a; cache_hit : bool; memory : int; time: float }

  let make ?(cache_hit=false) ~time res =
    (* This is quite slow! *)
    (* let memory = Obj.magic res |> Obj.reachable_words in *)
    let memory = 0 in
    { res; cache_hit; memory; time }

end

(* This requires a ppx likely as to ignore the CAst location *)
module VernacInput = struct

  type t = Coq_ast.t * Vernacstate.t

  let equal (v1, st1) (v2, st2) =
    if Coq_ast.compare v1 v2 = 0
    then
      if compare st1 st2 = 0
      then true
      else false
    else false

  let hash (v, st) = Hashtbl.hash (Coq_ast.hash v, st)

end

let input_info (v,st) =
  Format.asprintf "stm: %d | st %d" (Coq_ast.hash v) (Hashtbl.hash st)

module HC = Hashtbl.Make(VernacInput)

type cache = Vernacstate.t Coq_interp.interp_result HC.t
let cache : cache ref = ref (HC.create 1000)

let in_cache st stm =
  let kind = CS.Kind.Hashing in
  CS.record ~kind ~f:(HC.find_opt !cache) (stm, st)

let interp_command ~st stm : _ result Stats.t =
  match in_cache st stm with
  | Some st, time ->
    Lsp.Io.log_error "coq" "cache hit";
    Stats.make ~cache_hit:true ~time st
  | None, time_hash ->
    Lsp.Io.log_error "coq" "cache miss";
    let kind = CS.Kind.Exec in
    let res, time_interp = CS.record ~kind ~f:(Coq_interp.interp ~st) stm in
    let () = HC.add !cache (stm,st) res in
    let time = time_hash +. time_interp in
    Stats.make ~time res

let mem_stats () = Obj.reachable_words (Obj.magic cache)

let load_from_disk ~file =
  let in_c = open_in_bin file in
  let in_cache : cache = Marshal.from_channel in_c in
  cache := in_cache;
  close_in in_c

let save_to_disk ~file =
  let out_c = open_out_bin file in
  let out_cache : cache = !cache in
  Marshal.to_channel out_c out_cache [Closures];
  close_out out_c
