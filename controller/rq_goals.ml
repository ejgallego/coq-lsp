(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(* Replace by ppx when we can print goals properly in the client *)
let mk_message (range, level, text) = Lsp.JFleche.Message.{ range; level; text }

let mk_messages node =
  Option.map Fleche.Doc.Node.messages node
  |> Option.cata (List.map mk_message) []

let mk_error node =
  let open Fleche in
  let open Lang in
  match
    List.filter (fun d -> d.Diagnostic.severity < 2) node.Doc.Node.diags
  with
  | [] -> None
  | e :: _ -> Some e.Diagnostic.message

let goals_mode =
  if !Fleche.Config.v.goal_after_tactic then Fleche.Info.PrevIfEmpty
  else Fleche.Info.Prev

let goals ~doc ~point =
  let open Fleche in
  let goals = Info.LC.goals ~doc ~point goals_mode in
  let node = Info.LC.node ~doc ~point Exact in
  let messages = mk_messages node in
  let error = Option.bind node mk_error in
  let position =
    Lang.Point.{ line = fst point; character = snd point; offset = -1 }
  in
  Lsp.JFleche.mk_goals ~uri:doc.uri ~version:doc.version ~position ~goals
    ~messages ~error
