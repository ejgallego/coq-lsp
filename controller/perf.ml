(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

let rec list_take n = function
  | [] -> []
  | x :: xs -> if n = 0 then [] else x :: list_take (n - 1) xs

let mk_loc_time (n : Fleche.Doc.Node.t) =
  let time = Option.default 0.0 n.info.time in
  let mem = n.info.mw_after -. n.info.mw_prev in
  let loc = n.Fleche.Doc.Node.range in
  Lsp.JFleche.SentencePerfData.{ loc; time; mem }

let get_stats ~(doc : Fleche.Doc.t) =
  match List.rev doc.nodes with
  | [] -> "no stats"
  | n :: _ -> Fleche.Stats.to_string n.info.stats

(** Turn into a config option at some point? This is very expensive *)
let display_cache_size = false

let make (doc : Fleche.Doc.t) =
  let n_stm = List.length doc.nodes in
  let stats = get_stats ~doc in
  let cache_size =
    if display_cache_size then Fleche.Memo.Interp.size () |> float_of_int
    else 0.0
  in
  let summary =
    Format.asprintf "{ num sentences: %d@\n; stats: %s; cache: %a@\n}" n_stm
      stats Fleche.Stats.pp_words cache_size
  in
  let top =
    List.stable_sort
      (fun (n1 : Fleche.Doc.Node.t) n2 -> compare n2.info.time n1.info.time)
      doc.nodes
  in
  let top = list_take 10 top in
  let timings = List.map mk_loc_time top in
  Lsp.JFleche.DocumentPerfData.({ summary; timings } |> to_yojson)
