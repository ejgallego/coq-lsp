open Fleche

(* Put these in an utility function for plugins *)
let of_execution ~io ~what (v : (_, _) Coq.Protect.E.t) =
  match v with
  | { r; feedback = _ } -> (
    match r with
    | Coq.Protect.R.Completed (Ok goals) -> goals
    | Coq.Protect.R.Completed (Error (Anomaly { msg; _ }))
    | Coq.Protect.R.Completed (Error (User { msg; _ })) ->
      let lvl = Io.Level.Error in
      Io.Report.msg ~io ~lvl "error when retrieving %s: %a" what Pp.pp_with msg;
      None
    | Coq.Protect.R.Interrupted -> None)

(* We output a record for each sentence in the document, linear order. Note that
   for unparseable nodes, we don't have an AST. *)
module AstGoals = struct
  open Serializers
  open Sexplib.Conv

  type 'a t =
    { raw : string
    ; range : Lang.Range.t
    ; ast : Coq.Ast.t option
    ; goals : 'a Coq.Goals.reified_pp option
    }
  [@@deriving to_yojson, sexp_of]

  let of_node ~io ~token ~(contents : Contents.t) (node : Doc.Node.t) =
    let range = node.range in
    let raw = Fleche.Contents.extract_raw ~contents ~range in
    let ast = Option.map (fun n -> n.Doc.Node.Ast.v) node.ast in
    let st = node.state in
    let goals = of_execution ~io ~what:"goals" (Info.Goals.goals ~token ~st) in
    { raw; range; ast; goals }
end

let pp_json pp fmt (astgoal : _ AstGoals.t) =
  AstGoals.to_yojson pp astgoal |> Yojson.Safe.pretty_print fmt

(* For now we have not added sexp serialization, but we can easily do so *)
let pp_sexp pp fmt (astgoal : _ AstGoals.t) =
  AstGoals.sexp_of_t pp astgoal |> Sexplib.Sexp.pp_hum fmt

let pw pp fmt v = Format.fprintf fmt "@[%a@]@\n" pp v

let pp_ast_goals ~io ~token ~contents pp fmt node =
  AstGoals.of_node ~io ~token ~contents node |> pw pp fmt

let dump_goals ~io ~token ~out_file ~(doc : Doc.t) pp =
  let contents = doc.contents in
  let f fmt nodes =
    List.iter (pp_ast_goals ~io ~token ~contents pp fmt) nodes
  in
  Coq.Compat.format_to_file ~file:out_file ~f doc.nodes

(* Set to true to output Pp-formatted goals, should be a plugin option *)
let output_pp = false

let pp_j d =
  if output_pp then Fleche_lsp.JCoq.Pp.to_yojson d
  else `String (Pp.string_of_ppcmds d)

let pp_s d =
  if output_pp then Serlib.Ser_pp.sexp_of_t d
  else Sexplib.Sexp.Atom (Pp.string_of_ppcmds d)

let dump_ast ~io ~token ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[goaldump plugin] dumping goals for %s ..." uri_str;
  let out_file_j = Lang.LUri.File.to_string_file uri ^ ".json.goaldump" in
  let () = dump_goals ~io ~token ~out_file:out_file_j ~doc (pp_json pp_j) in
  let out_file_s = Lang.LUri.File.to_string_file uri ^ ".sexp.goaldump" in
  let () = dump_goals ~io ~token ~out_file:out_file_s ~doc (pp_sexp pp_s) in
  Io.Report.msg ~io ~lvl "[goaldump plugin] dumping ast for %s was completed!"
    uri_str;
  ()

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
