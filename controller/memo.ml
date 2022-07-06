module CS = Stats

module Stats = struct
  type 'a t =
    { res : 'a
    ; cache_hit : bool
    ; memory : int
    ; time : float
    }

  let make ?(cache_hit = false) ~time res =
    (* This is quite slow! *)
    (* let memory = Obj.magic res |> Obj.reachable_words in *)
    let memory = 0 in
    { res; cache_hit; memory; time }
end

(* This requires a ppx likely as to ignore the CAst location *)
module VernacInput = struct
  type t = Coq_ast.t * Coq_state.t

  let equal (v1, st1) (v2, st2) =
    if Coq_ast.compare v1 v2 = 0 then
      if Coq_state.compare st1 st2 = 0 then true else false
    else false

  let hash (v, st) = Hashtbl.hash (Coq_ast.hash v, st)

  let marshal_out oc (v, st) =
    Coq_ast.marshal_out oc v;
    Coq_state.marshal_out oc st;
    ()

  let marshal_in ic =
    let v = Coq_ast.marshal_in ic in
    let st = Coq_state.marshal_in ic in
    (v, st)
end

module CacheStats = struct
  let nhit, ntotal = (ref 0, ref 0)

  let reset () =
    nhit := 0;
    ntotal := 0

  let hit () =
    incr nhit;
    incr ntotal

  let miss () = incr ntotal

  let stats () =
    if !ntotal = 0 then "no stats"
    else
      let hit_rate =
        Stdlib.Float.of_int !nhit /. Stdlib.Float.of_int !ntotal *. 100.0
      in
      Format.asprintf "cache hit rate: %3.2f@\n" hit_rate
end

let input_info (v, st) =
  Format.asprintf "stm: %d | st %d" (Coq_ast.hash v) (Hashtbl.hash st)

module HC = Hashtbl.Make (VernacInput)

module Result = struct
  type t = Coq_state.t Coq_interp.interp_result

  let marshal_in ic : t = Coq_interp.marshal_in Coq_state.marshal_in ic
  let marshal_out oc t = Coq_interp.marshal_out Coq_state.marshal_out oc t
end

type cache = Result.t HC.t

let cache : cache ref = ref (HC.create 1000)

let in_cache st stm =
  let kind = CS.Kind.Hashing in
  CS.record ~kind ~f:(HC.find_opt !cache) (stm, st)

let interp_command ~st stm : _ result Stats.t =
  match in_cache st stm with
  | Some st, time ->
    Lsp.Io.log_error "coq" "cache hit";
    CacheStats.hit ();
    Stats.make ~cache_hit:true ~time st
  | None, time_hash ->
    Lsp.Io.log_error "coq" "cache miss";
    CacheStats.miss ();
    let kind = CS.Kind.Exec in
    let res, time_interp = CS.record ~kind ~f:(Coq_interp.interp ~st) stm in
    let () = HC.add !cache (stm, st) res in
    let time = time_hash +. time_interp in
    Stats.make ~time res

let mem_stats () = Obj.reachable_words (Obj.magic cache)

let _hashtbl_out oc t =
  Marshal.to_channel oc (HC.length t) [];
  HC.iter
    (fun vi res ->
      VernacInput.marshal_out oc vi;
      Result.marshal_out oc res)
    t

let _hashtbl_in ic =
  let ht = HC.create 1000 in
  let count : int = Marshal.from_channel ic in
  for _i = 0 to count - 1 do
    let vi = VernacInput.marshal_in ic in
    let res = Result.marshal_in ic in
    HC.add ht vi res
  done;
  ht

let load_from_disk ~file =
  let ic = open_in_bin file in
  (* let in_cache : cache = hashtbl_in in_c in *)
  let in_cache : cache = Marshal.from_channel ic in
  cache := in_cache;
  close_in ic

let save_to_disk ~file =
  let oc = open_out_bin file in
  let out_cache : cache = !cache in
  Marshal.to_channel oc out_cache [];
  (* hashtbl_out out_c out_cache; *)
  close_out oc
