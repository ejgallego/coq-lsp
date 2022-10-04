(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2022 Inria           -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

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

  let marshal_out oc (v, st) =
    Coq.Ast.marshal_out oc v;
    Coq.State.marshal_out oc st;
    ()

  let marshal_in ic =
    let v = Coq.Ast.marshal_in ic in
    let st = Coq.State.marshal_in ic in
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
  Format.asprintf "stm: %d | st %d" (Coq.Ast.hash v) (Hashtbl.hash st)

module HC = Hashtbl.Make (VernacInput)

module Result = struct
  (* We store the location as to compute an offset for cached results *)
  type t = Loc.t * Coq.State.t Coq.Interp.interp_result

  (* XXX *)
  let marshal_in ic : t =
    let loc = Marshal.from_channel ic in
    (loc, Coq.Interp.marshal_in Coq.State.marshal_in ic)

  let marshal_out oc (loc, t) =
    Marshal.to_channel oc loc [];
    Coq.Interp.marshal_out Coq.State.marshal_out oc t
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
  Coq.Protect.map_loc ~f res

let interp_command ~st ~fb_queue stm : _ Stats.t =
  let stm_loc = Coq.Ast.loc stm |> Option.get in
  match in_cache st stm with
  | Some (cached_loc, res), time ->
    if Debug.cache then Io.Log.error "coq" "cache hit";
    CacheStats.hit ();
    let res = adjust_offset ~stm_loc ~cached_loc res in
    Stats.make ~cache_hit:true ~time res
  | None, time_hash -> (
    if Debug.cache then Io.Log.error "coq" "cache miss";
    CacheStats.miss ();
    let kind = CS.Kind.Exec in
    let res, time_interp =
      CS.record ~kind ~f:(Coq.Interp.interp ~st ~fb_queue) stm
    in
    let time = time_hash +. time_interp in
    match res with
    | Coq.Protect.R.Interrupted as res ->
      (* Don't cache interruptions *)
      fb_queue := [];
      Stats.make ~time res
    | Coq.Protect.R.Completed _ as res ->
      let () = HC.add !cache (stm, st) (stm_loc, res) in
      let time = time_hash +. time_interp in
      Stats.make ~time res)

let mem_stats () = Obj.reachable_words (Obj.magic cache)

module ParseInput = struct
  type t = Pvernac.proof_mode option * Vernacstate.Parser.t * Span.t

  let hash x = Hashtbl.hash x
  let equal x y = compare x y = 0
end

module PC = Hashtbl.Make (ParseInput)

let parse_coq ~mode ~st ps =
  let parse ps =
    (* Coq is missing this, so we add it here. Note that this MUST run inside
       Coq.Protect. *)
    Control.check_for_interrupt ();
    Vernacstate.Parser.parse st Pvernac.(main_entry mode) ps
    |> Option.map Coq.Ast.of_coq
  in
  Coq.Protect.eval ~f:parse ps

(* What about parsing stats? *)
(* Stats.record ~kind:Stats.Kind.Parsing ~f:(Coq.Protect.eval ~f:parse) ps *\) *)

let loc_of_parse_res loc res =
  match res with
  | Ok (Some res) -> Option.get (Coq.Ast.loc res)
  | Ok None -> loc (* EOF = end loc == start loc *)
  | Error (loc, _) -> Option.get loc

let lcache = Hashtbl.create 1000
let pcache = PC.create 1000

let in_parse_cache mode st text ps =
  let kind = CS.Kind.Hashing in
  let stream_loc = Pcoq.Parsable.loc ps in
  match Hashtbl.find_opt lcache stream_loc with
  | None -> (None, 0.0)
  | Some ast_loc ->
    Io.Log.error "in_parse_cache" "start pos in segment cache";
    (* Mmmmm, this seems tricky *)
    let span = Span.make ~contents:text ~loc:ast_loc in
    let loc_pr = Loc.pr ast_loc |> Pp.string_of_ppcmds in
    Io.Log.error "coq" ("query parse cache: " ^ loc_pr ^ " | " ^ span.text);
    let f key =
      PC.find_opt pcache key
      |> Option.map (fun hit -> (hit, String.length span.text))
    in
    CS.record ~kind ~f (mode, st, span)

let parse ~mode ~st ~text ps =
  match in_parse_cache mode st text ps with
  | Some (res, skip), time ->
    Io.Log.error "coq" "parse cache hit";
    CacheStats.hit ();
    Pcoq.Parsable.consume ps skip;
    (* Stats.make ~cache_hit:true ~time st *)
    (res, time)
  | None, time_hash -> (
    Io.Log.error "coq" "parse cache miss";
    CacheStats.miss ();
    let kind = CS.Kind.Parsing in
    let f = parse_coq ~mode ~st in
    let stream_loc = Pcoq.Parsable.loc ps in
    let res, time_parse = CS.record ~kind ~f ps in
    let time = time_hash +. time_parse in
    match res with
    | Coq.Protect.R.Interrupted ->
      (* We don't cache *)
      (res, time)
    | Coq.Protect.R.Completed pres ->
      let ast_loc = loc_of_parse_res stream_loc pres in
      let span = Span.make ~contents:text ~loc:ast_loc in
      let () = Hashtbl.add lcache stream_loc ast_loc in
      let loc_pr = Loc.pr ast_loc |> Pp.string_of_ppcmds in
      Io.Log.error "coq" ("add to parse cache: " ^ loc_pr ^ " | " ^ span.text);
      let () = PC.add pcache (mode, st, span) res in
      (* let _ = Pcoq.Parsable.t *)
      (res, time))

(* Strategy to cache parsing:

   We will use a table: (mode, pstate, start_loc, text_segment) -> parse_result

   + After parsing we must compute text_segment, that is not easy with Coq API.
   Use the document from LSP for now.

   + We also need to know the start loc, we need to tweak Coq's API.

   We check we have the same starting pos, state, mode, segment (using LSP or
   npeek work here) If cache hit, great! drop n elements, otherwise, parse. *)

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
