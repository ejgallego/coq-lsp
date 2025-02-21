(************************************************************************)
(* Coq Language Server Protocol -- Document                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module JFleche = Fleche_lsp.JFleche

let to_span { Fleche.Doc.Node.range; ast; _ } =
  let span = Option.map (fun { Fleche.Doc.Node.Ast.v; _ } -> v) ast in
  JFleche.RangedSpan.{ range; span }

let to_completed = function
  | Fleche.Doc.Completion.Yes range ->
    { JFleche.CompletionStatus.status = `Yes; range }
  | Stopped range -> { status = `Stopped; range }
  | Failed range -> { status = `Failed; range }

let request ~token:_ ~doc =
  let { Fleche.Doc.nodes; completed; _ } = doc in
  let spans = List.map to_span nodes in
  let completed = to_completed completed in
  JFleche.FlecheDocument.({ spans; completed } |> to_yojson) |> Result.ok
