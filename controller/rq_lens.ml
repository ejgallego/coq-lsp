(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

let command ~point =
  let arguments = Some [ Lsp.JLang.Point.to_yojson point ] in
  Lsp.Core.Command.
    { title = "Show goals"; command = "coq-lsp.goals"; arguments }

let mk_goals_lens (node : Fleche.Doc.Node.t) =
  let point = node.range.start in
  Lsp.Core.CodeLens.(
    { range = node.range; command = Some (command ~point); data = None }
    |> to_yojson)

(* Example lens to show goals, seems that args are not working *)
let _goals_lens ~(doc : Fleche.Doc.t) = `List (List.map mk_goals_lens doc.nodes)

let request ~doc:_ = `Null
