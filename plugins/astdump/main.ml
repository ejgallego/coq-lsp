open Fleche

let pp_json fmt (ast : Doc.Node.Ast.t) =
  Lsp.JCoq.Ast.to_yojson ast.v |> Yojson.Safe.pretty_print fmt

let pp_sexp fmt (ast : Doc.Node.Ast.t) =
  Serlib.Ser_vernacexpr.sexp_of_vernac_control (Coq.Ast.to_coq ast.v)
  |> Sexplib.Sexp.pp_hum fmt

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
  let out_file_j = Lang.LUri.File.to_string_file uri ^ ".json.astdump" in
  let () = dump_asts ~out_file:out_file_j pp_json asts in
  (* Output sexp *)
  let out_file_s = Lang.LUri.File.to_string_file uri ^ ".sexp.astdump" in
  let () = dump_asts ~out_file:out_file_s pp_sexp asts in
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s was completed!"
    uri_str;
  ()

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
