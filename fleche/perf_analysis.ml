open Perf

let rec list_take n = function
  | [] -> []
  | x :: xs -> if n = 0 then [] else x :: list_take (n - 1) xs

let mk_info (n : Doc.Node.t) =
  let time, memory, cache_hit, time_hash =
    Option.cata
      (fun (stats : Memo.Stats.t) ->
        (stats.stats.time, stats.stats.memory, stats.cache_hit, stats.time_hash))
      (0.0, 0.0, false, 0.0) n.info.stats
  in
  Info.{ time; memory; cache_hit; time_hash }

let mk_sentence (n : Doc.Node.t) =
  let range = n.range in
  let info = mk_info n in
  Sentence.{ range; info }

let get_stats ~(doc : Doc.t) =
  match List.rev doc.nodes with
  | [] -> "no global stats"
  | n :: _ -> Stats.Global.to_string n.info.global_stats

(** Turn into a config option at some point? This is very expensive *)
let display_cache_size = false

let node_time_compare (n1 : Doc.Node.t) (n2 : Doc.Node.t) =
  match (n1.info.stats, n2.info.stats) with
  | Some s1, Some s2 -> -compare s1.stats.time s2.stats.time
  | None, Some _ -> 1
  | Some _, None -> -1
  | None, None -> 0

(* Old mode of sending only the 10 hotspots *)
let hotspot = false

let make (doc : Doc.t) =
  let n_stm = List.length doc.nodes in
  let stats = get_stats ~doc in
  let cache_size =
    if display_cache_size then Memo.all_size () |> float_of_int else 0.0
  in
  let summary =
    Format.asprintf "{ num sentences: %d@\n; stats: %s; cache: %a@\n}" n_stm
      stats Stats.pp_words cache_size
  in
  let timings =
    if hotspot then List.stable_sort node_time_compare doc.nodes |> list_take 10
    else doc.nodes
  in
  let timings = List.map mk_sentence timings in
  { summary; timings }
