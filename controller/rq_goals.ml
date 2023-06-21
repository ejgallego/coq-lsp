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

let get_goals_mode () =
  if !Fleche.Config.v.goal_after_tactic then Fleche.Info.PrevIfEmpty
  else Fleche.Info.Prev

(** Format for goal printing *)
type format =
  | Pp
  | Str

let pp ~pp_format pp =
  match pp_format with
  | Pp -> Lsp.JCoq.Pp.to_yojson pp
  | Str -> `String (Pp.string_of_ppcmds pp)

let goals ~token ~pp_format ~doc ~point =
  let open Fleche in
  let uri, version = (doc.Doc.uri, doc.version) in
  let textDocument = Lsp.Doc.VersionedTextDocumentIdentifier.{ uri; version } in
  let position =
    Lang.Point.{ line = fst point; character = snd point; offset = -1 }
  in
  let goals_mode = get_goals_mode () in
  let goals = Info.LC.goals ~token ~doc ~point goals_mode in
  let program = Info.LC.program ~doc ~point goals_mode in
  let node = Info.LC.node ~doc ~point Exact in
  let messages = mk_messages node in
  let error = Option.bind node mk_error in
  let pp = pp ~pp_format in
  Lsp.JFleche.GoalsAnswer.(
    to_yojson pp { textDocument; position; goals; program; messages; error })
  |> Result.ok
