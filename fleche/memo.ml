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
  type t = Coq.Ast.t * Coq.State.t

  let equal (v1, st1) (v2, st2) =
    if Coq.Ast.compare v1 v2 = 0 then
      if Coq.State.compare st1 st2 = 0 then true else false
    else false

  let hash (v, st) = Hashtbl.hash (Coq.Ast.hash v, st)
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
      Format.asprintf "cache hit rate: %3.2f" hit_rate
end

let input_info (v, st) =
  Format.asprintf "stm: %d | st %d" (Coq.Ast.hash v) (Hashtbl.hash st)

module HC = Hashtbl.Make (VernacInput)

module Result = struct
  (* We store the location as to compute an offset for cached results *)
  type t = Loc.t * Coq.State.t Coq.Interp.interp_result
end

type cache = Result.t HC.t

let cache : cache ref = ref (HC.create 1000)

let in_cache st stm =
  let kind = CS.Kind.Hashing in
  CS.record ~kind ~f:(HC.find_opt !cache) (stm, st)

(* XXX: Move elsewhere *)
let loc_offset (l1 : Loc.t) (l2 : Loc.t) =
  let line_offset = l2.line_nb - l1.line_nb in
  let bol_offset = l2.bol_pos - l1.bol_pos in
  let line_last_offset = l2.line_nb_last - l1.line_nb_last in
  let bol_last_offset = l2.bol_pos_last - l1.bol_pos_last in
  let bp_offset = l2.bp - l1.bp in
  let ep_offset = l2.ep - l1.ep in
  ( line_offset
  , bol_offset
  , line_last_offset
  , bol_last_offset
  , bp_offset
  , ep_offset )

let loc_apply_offset
    ( line_offset
    , bol_offset
    , line_last_offset
    , bol_last_offset
    , bp_offset
    , ep_offset ) (loc : Loc.t) =
  { loc with
    line_nb = loc.line_nb + line_offset
  ; bol_pos = loc.bol_pos + bol_offset
  ; line_nb_last = loc.line_nb_last + line_last_offset
  ; bol_pos_last = loc.bol_pos_last + bol_last_offset
  ; bp = loc.bp + bp_offset
  ; ep = loc.ep + ep_offset
  }

let adjust_offset ~stm_loc ~cached_loc res =
  let offset = loc_offset cached_loc stm_loc in
  let f = loc_apply_offset offset in
  Coq.Protect.E.map_loc ~f res

let interp_command ~st stm : _ Stats.t =
  let stm_loc = Coq.Ast.loc stm |> Option.get in
  match in_cache st stm with
  | Some (cached_loc, res), time ->
    if Debug.cache then Io.Log.trace "memo" "cache hit";
    CacheStats.hit ();
    let res = adjust_offset ~stm_loc ~cached_loc res in
    Stats.make ~cache_hit:true ~time res
  | None, time_hash -> (
    if Debug.cache then Io.Log.trace "memo" "cache miss";
    CacheStats.miss ();
    let kind = CS.Kind.Exec in
    let res, time_interp = CS.record ~kind ~f:(Coq.Interp.interp ~st) stm in
    let time = time_hash +. time_interp in
    match res.r with
    | Coq.Protect.R.Interrupted ->
      (* Don't cache interruptions *)
      Stats.make ~time res
    | Coq.Protect.R.Completed _ ->
      let () = HC.add !cache (stm, st) (stm_loc, res) in
      let time = time_hash +. time_interp in
      Stats.make ~time res)

module AC = Hashtbl.Make (Coq.State)

let admit_cache = AC.create 1000

let interp_admitted ~st =
  match AC.find_opt admit_cache st with
  | None ->
    let admitted_st = Coq.State.admit ~st in
    AC.add admit_cache st admitted_st;
    admitted_st
  | Some admitted_st -> admitted_st

let mem_stats () = Obj.reachable_words (Obj.magic cache)

(* let _hashtbl_out oc t = () *)
(* Marshal.to_channel oc (HC.length t) []; *)
(* HC.iter *)
(*   (fun vi res -> *)
(*     VernacInput.marshal_out oc vi; *)
(*     Result.marshal_out oc res) *)
(*   t *)

(* let _hashtbl_in ic = *)
(*   let ht = HC.create 1000 in *)
(*   let count : int = Marshal.from_channel ic in *)
(*   for _i = 0 to count - 1 do *)
(*     let vi = VernacInput.marshal_in ic in *)
(*     let res = Result.marshal_in ic in *)
(*     HC.add ht vi res *)
(*   done; *)
(*   ht *)

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
