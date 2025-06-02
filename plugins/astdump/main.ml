(************************************************************************)
(* Flèche / coq-lsp                                                     *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2024-2025 Emilio J. Gallego Arias -- LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)

module Lsp = Fleche_lsp
open Fleche

(* XXX: Allow users to select this using the plugin argument system *)
(* If [true], we print  *)
let pretty_print = false

let pp_json fmt obj =
  if pretty_print then Yojson.Safe.pretty_print fmt obj
  else Format.fprintf fmt "@[%s@\n@]" (Yojson.Safe.to_string obj)

let pp_ast_json fmt (ast : Doc.Node.Ast.t) =
  Lsp.JCoq.Ast.to_yojson ast.v |> pp_json fmt

let pp_sexp fmt obj =
  if pretty_print then Sexplib.Sexp.pp_hum fmt obj
  else Format.fprintf fmt "@[%a@\n@]" Sexplib.Sexp.pp obj

let pp_ast_sexp fmt (ast : Doc.Node.Ast.t) =
  Serlib.Ser_vernacexpr.sexp_of_vernac_control (Coq.Ast.to_coq ast.v)
  |> pp_sexp fmt

let pw pp fmt ast = Format.fprintf fmt "@[%a@]" pp ast

let dump_asts ~out_file pp asts =
  let f fmt asts = List.iter (pw pp fmt) asts in
  Coq.Compat.format_to_file ~file:out_file ~f asts

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s ..." uri_str;
  let asts = Doc.asts doc in
  (* Output json *)
  let out_file_j = Lang.LUri.File.to_string_file uri ^ ".jsonl.astdump" in
  let () = dump_asts ~out_file:out_file_j pp_ast_json asts in
  (* Output sexp *)
  let out_file_s = Lang.LUri.File.to_string_file uri ^ ".sexpl.astdump" in
  let () = dump_asts ~out_file:out_file_s pp_ast_sexp asts in
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s was completed!"
    uri_str;
  ()

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
