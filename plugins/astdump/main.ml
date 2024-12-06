open Fleche

type outputFormat = Json | Sexp

let ast_to_json (ast : Doc.Node.Ast.t) =
  Lsp.JCoq.Ast.to_yojson ast.v

let ast_to_sexp_string (ast : Doc.Node.Ast.t) =
  Serlib.Ser_vernacexpr.sexp_of_vernac_control (Coq.Ast.to_coq ast.v)
  |> Sexplib.Sexp.to_string_hum


let dump_asts ~out_file (asts: Doc.Node.Ast.t list) output_format =
    let out_chan = open_out out_file in
    match output_format with 
     Json -> 
         Yojson.Safe.pretty_to_channel out_chan (`List (List.map ast_to_json asts));
    | Sexp -> 
         output_string out_chan  (List.map (fun ast -> ast_to_sexp_string ast) asts |> String.concat "\n")

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s ..." uri_str;
  let asts = Doc.asts doc in
  (* Output json *)
  let out_file_j = Lang.LUri.File.to_string_file uri ^ ".json.astdump" in
  dump_asts ~out_file:out_file_j asts Json;
  (* Output sexp *)
  let out_file_s = Lang.LUri.File.to_string_file uri ^ ".sexp.astdump" in
  dump_asts ~out_file:out_file_s asts Sexp;
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s was completed!"
    uri_str;
  ()

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
