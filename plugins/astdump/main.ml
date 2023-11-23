open Fleche

let pp_json fmt (ast : Doc.Node.Ast.t) =
  let jast = Lsp.JCoq.Ast.to_yojson ast.v in
  Yojson.Safe.pretty_print fmt jast

let pp_sexp fmt (ast : Doc.Node.Ast.t) =
  let sast =
    Serlib.Ser_vernacexpr.sexp_of_vernac_control (Coq.Ast.to_coq ast.v)
  in
  Sexplib.Sexp.pp_hum fmt sast

let pw pp fmt ast = Format.fprintf fmt "@[%a@]" pp ast

let dump_asts ~out_file pp asts =
  let out = Stdlib.open_out out_file in
  let fmt = Format.formatter_of_out_channel out in
  List.iter (pw pp fmt) asts;
  Format.pp_print_flush fmt ();
  Stdlib.close_out out

let dump_ast ~io ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let out_file_j = Lang.LUri.File.to_string_file uri ^ ".json.astdump" in
  let out_file_s = Lang.LUri.File.to_string_file uri ^ ".sexp.astdump" in
  let lvl = Io.Level.info in
  let message = Format.asprintf "[ast plugin] dumping ast for %s ..." uri_str in
  Io.Report.message ~io ~lvl ~message;
  let asts = Doc.asts doc in
  let () = dump_asts ~out_file:out_file_j pp_json asts in
  let () = dump_asts ~out_file:out_file_s pp_sexp asts in
  let message =
    Format.asprintf "[ast plugin] dumping ast for %s was completed!" uri_str
  in
  Io.Report.message ~io ~lvl ~message;
  ()

let main () = Theory.Register.add dump_ast
let () = main ()
