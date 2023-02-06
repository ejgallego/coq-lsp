(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

open Lsp.JFleche

let hover ~doc ~point =
  let show_loc_info = true in
  let range_span = Fleche.Info.LC.range ~doc ~point Exact in
  let range_string =
    let none fmt () = Format.fprintf fmt "no ast" in
    Format.asprintf "%a" (Format.pp_print_option ~none Lang.Range.pp) range_span
  in
  let info_string =
    Fleche.Info.LC.info ~doc ~point Exact
    |> Option.map Fleche.Doc.Node.Info.print
    |> Option.default "no info"
  in
  let hover_string =
    if show_loc_info then range_string ^ "\n___\n" ^ info_string
    else info_string
  in
  let contents = { HoverContents.kind = "markdown"; value = hover_string } in
  let range = range_span in
  HoverInfo.(to_yojson { contents; range })
