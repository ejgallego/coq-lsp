open Perf

let rec list_take n = function
  | [] -> []
  | x :: xs -> if n = 0 then [] else x :: list_take (n - 1) xs

let mk_loc_time (n : Doc.Node.t) =
  let time = Option.default 0.0 n.info.time in
  let mem = n.info.mw_after -. n.info.mw_prev in
  let loc = n.Doc.Node.range in
  Sentence.{ loc; time; mem }

let get_stats ~(doc : Doc.t) =
  match List.rev doc.nodes with
  | [] -> "no stats"
  | n :: _ -> Stats.to_string n.info.stats

(** Turn into a config option at some point? This is very expensive *)
let display_cache_size = false

let make (doc : Doc.t) =
  let n_stm = List.length doc.nodes in
  let stats = get_stats ~doc in
  let cache_size =
    if display_cache_size then Memo.Interp.size () |> float_of_int else 0.0
  in
  let summary =
    Format.asprintf "{ num sentences: %d@\n; stats: %s; cache: %a@\n}" n_stm
      stats Stats.pp_words cache_size
  in
  let top =
    List.stable_sort
      (fun (n1 : Doc.Node.t) n2 -> compare n2.info.time n1.info.time)
      doc.nodes
  in
  let top = list_take 10 top in
  let timings = List.map mk_loc_time top in
  { summary; timings }
