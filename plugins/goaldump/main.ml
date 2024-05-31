open Fleche

(* Put these in an utility function for plugins *)
let of_execution ~io ~what (v : (_, _) Coq.Protect.E.t) =
  match v with
  | { r; feedback = _ } -> (
    match r with
    | Coq.Protect.R.Completed (Ok goals) -> goals
    | Coq.Protect.R.Completed (Error (Anomaly err))
    | Coq.Protect.R.Completed (Error (User err)) ->
      let message =
        Format.asprintf "error when retrieving %s: %a" what Pp.pp_with (snd err)
      in
      Io.Report.message ~io ~lvl:Io.Level.error ~message;
      None
    | Coq.Protect.R.Interrupted -> None)

(* We output a record for each sentence in the document, linear order. Note that
   for unparseable nodes, we don't have an AST. *)
module AstGoals = struct
  (* Just to bring the serializers in scope *)
  module Lang = Lsp.JLang
  module Coq = Lsp.JCoq

  type 'a t =
    { raw : string
    ; range : Lang.Range.t
    ; ast : Coq.Ast.t option
    ; goals : 'a Coq.Goals.reified_pp option
    }
  [@@deriving to_yojson]

  let of_node ~io ~token ~(contents : Contents.t) (node : Doc.Node.t) =
    let range = node.range in
    let raw = Fleche.Contents.extract_raw ~contents ~range in
    let ast = Option.map (fun n -> n.Doc.Node.Ast.v) node.ast in
    let st = node.state in
    let goals = of_execution ~io ~what:"goals" (Info.Goals.goals ~token ~st) in
    { raw; range; ast; goals }
end

let pp_json pp fmt (astgoal : _ AstGoals.t) =
  let g_json = AstGoals.to_yojson pp astgoal in
  Yojson.Safe.pretty_print fmt g_json

(* For now we have not added sexp serialization, but we can easily do so *)
(* let pp_sexp fmt (astgoal : AstGoals.t) = *)
(*   let g_sexp = AstGoals.sexp_of astgoal in *)
(*   Sexplib.Sexp.pp_hum fmt sast *)

let pw pp fmt v = Format.fprintf fmt "@[%a@]@\n" pp v

let pp_ast_goals ~io ~token ~contents pp fmt node =
  let res = AstGoals.of_node ~io ~token ~contents node in
  pw pp fmt res

let dump_goals ~io ~token ~out_file ~(doc : Doc.t) pp =
  let out = Stdlib.open_out out_file in
  let fmt = Format.formatter_of_out_channel out in
  let contents = doc.contents in
  List.iter (pp_ast_goals ~io ~token ~contents pp fmt) doc.nodes;
  Format.pp_print_flush fmt ();
  Stdlib.close_out out

let dump_ast ~io ~token ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let message =
    Format.asprintf "[goaldump plugin] dumping goals for %s ..." uri_str
  in
  let lvl = Io.Level.info in
  Io.Report.message ~io ~lvl ~message;
  let out_file_j = Lang.LUri.File.to_string_file uri ^ ".json.goaldump" in
  let pp d = `String (Pp.string_of_ppcmds d) in
  (* Uncomment to output Pp-formatted goals *)
  (* let pp d = Lsp.JCoq.Pp.to_yojson d in *)
  let () = dump_goals ~io ~token ~out_file:out_file_j ~doc (pp_json pp) in
  (* let out_file_s = Lang.LUri.File.to_string_file uri ^ ".sexp.goaldump" in *)
  (* let () = dump_goals ~out_file:out_file_s ~doc pp_sexp in *)
  let message =
    Format.asprintf "[ast plugin] dumping ast for %s was completed!" uri_str
  in
  Io.Report.message ~io ~lvl ~message;
  ()

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
