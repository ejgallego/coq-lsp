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

module MemoTable = struct
  module type S = sig
    include Hashtbl.S

    val add_execution :
      ('a, 'l) Coq.Protect.E.t t -> key -> ('a, 'l) Coq.Protect.E.t -> unit

    val add_execution_loc :
         ('v * ('a, 'l) Coq.Protect.E.t) t
      -> key
      -> 'v * ('a, 'l) Coq.Protect.E.t
      -> unit
  end

  module Make (H : Hashtbl.HashedType) : S with type key = H.t = struct
    include Hashtbl.Make (H)

    let add_execution t k ({ Coq.Protect.E.r; _ } as v) =
      match r with
      | Coq.Protect.R.Interrupted -> ()
      | _ -> add t k v

    let add_execution_loc t k ((_, { Coq.Protect.E.r; _ }) as v) =
      match r with
      | Coq.Protect.R.Interrupted -> ()
      | _ -> add t k v
  end
end

module Interp = struct
  (* Loc-independent command evalution and caching. *)
  module VernacInput = struct
    type t = Coq.State.t * Coq.Ast.t

    (* This crutially relies on our ppx to ignore the CAst location *)
    let equal (st1, v1) (st2, v2) =
      if Coq.Ast.compare v1 v2 = 0 then
        if Coq.State.compare st1 st2 = 0 then true else false
      else false

    let hash (st, v) = Hashtbl.hash (Coq.Ast.hash v, st)
  end

  type t = VernacInput.t

  let input_info (st, v) =
    Format.asprintf "stm: %d | st %d" (Coq.Ast.hash v) (Hashtbl.hash st)

  module HC = MemoTable.Make (VernacInput)

  module Result = struct
    (* We store the location as to compute an offset for cached results *)
    type t = Loc.t * (Coq.State.t, Loc.t) Coq.Protect.E.t
  end

  type cache = Result.t HC.t

  let cache : cache ref = ref (HC.create 1000)

  (* This is very expensive *)
  let size () = Obj.reachable_words (Obj.magic cache)

  let in_cache st stm =
    let kind = CS.Kind.Hashing in
    CS.record ~kind ~f:(HC.find_opt !cache) (st, stm)

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

  let eval (st, stm) : _ Stats.t =
    let stm_loc = Coq.Ast.loc stm |> Option.get in
    match in_cache st stm with
    | Some (cached_loc, res), time ->
      if Debug.cache then Io.Log.trace "memo" "cache hit";
      CacheStats.hit ();
      let res = adjust_offset ~stm_loc ~cached_loc res in
      Stats.make ~cache_hit:true ~time res
    | None, time_hash ->
      if Debug.cache then Io.Log.trace "memo" "cache miss";
      CacheStats.miss ();
      let kind = CS.Kind.Exec in
      let res, time_interp = CS.record ~kind ~f:(Coq.Interp.interp ~st) stm in
      let () = HC.add_execution_loc !cache (st, stm) (stm_loc, res) in
      let time = time_hash +. time_interp in
      Stats.make ~time res
end

module Admit = struct
  type t = Coq.State.t

  module C = MemoTable.Make (Coq.State)

  let cache = C.create 1000

  let eval v =
    match C.find_opt cache v with
    | None ->
      let admitted_st = Coq.State.admit ~st:v in
      C.add_execution cache v admitted_st;
      admitted_st
    | Some admitted_st -> admitted_st
end

module Init = struct
  module S = struct
    type t = Coq.State.t * Coq.Workspace.t * Lang.LUri.File.t

    let equal (s1, w1, u1) (s2, w2, u2) : bool =
      if Lang.LUri.File.compare u1 u2 = 0 then
        if Coq.Workspace.compare w1 w2 = 0 then
          if Coq.State.compare s1 s2 = 0 then true else false
        else false
      else false

    let hash (st, w, uri) =
      Hashtbl.hash
        (Coq.State.hash st, Coq.Workspace.hash w, Lang.LUri.File.hash uri)
  end

  type t = S.t

  module C = MemoTable.Make (S)

  let cache = C.create 1000

  let eval v =
    match C.find_opt cache v with
    | None ->
      let root_state, workspace, uri = v in
      let admitted_st = Coq.Init.doc_init ~root_state ~workspace ~uri in
      C.add_execution cache v admitted_st;
      admitted_st
    | Some res -> res
end
