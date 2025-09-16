(************************************************************************)
(* Coq Language Server Protocol -- Document                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module JFleche = Fleche_lsp.JFleche

let mk_messages ~messages =
  List.map Fleche_lsp.JFleche.Message.of_coq_message messages

let mk_error ~diags =
  let open Lang in
  match List.filter Diagnostic.is_error diags with
  | [] -> None
  (* XXX FIXME! *)
  | e :: _ -> Some e.Diagnostic.message

let get_goal_info ~token ~pr ~st =
  let open Fleche in
  let open Coq.Protect.E.O in
  let+ goals = Info.Goals.goals ~token ~pr ~st in
  let program = Info.Goals.program ~st in
  (goals, Some program)

let get_goals ~token ~pr ~textDocument ~range ~state ~diags ~messages =
  let open Coq.Protect.E.O in
  let position = range.Lang.Range.start in
  let range = Some range in
  let+ goals, program = get_goal_info ~token ~pr ~st:state in
  let messages = mk_messages ~messages in
  let error = mk_error ~diags in
  Fleche_lsp.JFleche.GoalsAnswer.
    { textDocument; position; range; goals; program; messages; error }

let of_execution (v : (_, _) Coq.Protect.E.t) =
  match v with
  | { r; feedback = _ } -> (
    match r with
    | Coq.Protect.R.Completed (Ok goals) -> Some goals
    | Coq.Protect.R.Completed (Error (Anomaly { msg = _; _ }))
    | Coq.Protect.R.Completed (Error (User { msg = _; _ })) -> None
    | Coq.Protect.R.Interrupted -> None)

let to_span ~token ~pr ~ast ~goals ~textDocument
    { Fleche.Doc.Node.range; ast = nast; state; diags; messages; _ } =
  let ast =
    if ast then Option.map (fun { Fleche.Doc.Node.Ast.v; _ } -> v) nast
    else None
  in
  let goals =
    match goals with
    | None -> None
    | Some _ ->
      of_execution
        (get_goals ~token ~pr ~textDocument ~range ~state ~diags ~messages)
  in
  JFleche.RangedSpan.{ range; ast; goals }

let to_completed = function
  | Fleche.Doc.Completion.Yes range ->
    { JFleche.CompletionStatus.status = `Yes; range }
  | Stopped range -> { status = `Stopped; range }
  | Failed range -> { status = `Failed; range }

let request ~ast ~goals () ~token ~doc =
  let { Fleche.Doc.uri; version; nodes; completed; _ } = doc in
  let textDocument =
    Fleche_lsp.Doc.VersionedTextDocumentIdentifier.{ uri; version }
  in
  let pp_format =
    match goals with
    | None -> Rq_goals.Pp
    | Some pp -> pp
  in
  let pr = Rq_goals.pp ~pp_format in
  let spans = List.map (to_span ~token ~pr ~ast ~goals ~textDocument) nodes in
  let completed = to_completed completed in
  JFleche.FlecheDocument.(
    { spans; completed }
    |> to_yojson (fun x -> x) (fun x -> Fleche_lsp.JCoq.Pp.to_yojson x))
  |> Result.ok
