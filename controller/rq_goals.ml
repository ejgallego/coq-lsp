(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Lsp = Fleche_lsp

(* Replace by ppx when we can print goals properly in the client *)
let mk_messages node =
  Option.map Fleche.Doc.Node.messages node
  |> Option.cata (List.map Lsp.JFleche.Message.of_coq_message) []

let mk_error node =
  let open Fleche in
  let open Lang in
  match List.filter Diagnostic.is_error node.Doc.Node.diags with
  | [] -> None
  (* XXX FIXME! *)
  | e :: _ -> Some e.Diagnostic.message

(** Format for goal printing *)
type format =
  | Pp
  | Str

let pp ~pp_format pp =
  match pp_format with
  | Pp -> Lsp.JCoq.Pp.to_yojson pp
  | Str -> `String (Pp.string_of_ppcmds pp)

let run_pretac ~token ~loc ~st pretac =
  match pretac with
  | None -> Coq.Protect.E.ok st
  | Some tac -> Fleche.Doc.run ~token ?loc ~st tac

let get_goal_info ~token ~doc ~point ~mode ~pretac () =
  let open Fleche in
  let node = Info.LC.node ~doc ~point mode in
  match node with
  | None -> Coq.Protect.E.ok (None, None)
  | Some node ->
    let open Coq.Protect.E.O in
    let st = Doc.Node.state node in
    (* XXX: Get the location from node *)
    let loc = None in
    let* st = run_pretac ~token ~loc ~st pretac in
    let+ goals = Info.Goals.goals ~token ~st in
    let program = Info.Goals.program ~st in
    (goals, Some program)

let goals ~pp_format ~mode ~pretac () ~token ~doc ~point =
  let open Fleche in
  let uri, version = (doc.Doc.uri, doc.version) in
  let textDocument = Lsp.Doc.VersionedTextDocumentIdentifier.{ uri; version } in
  let position =
    Lang.Point.{ line = fst point; character = snd point; offset = -1 }
  in
  let open Coq.Protect.E.O in
  let+ goals, program = get_goal_info ~token ~doc ~point ~mode ~pretac () in
  let node = Info.LC.node ~doc ~point mode in
  let range = Option.map Fleche.Doc.Node.range node in
  let messages = mk_messages node in
  let error = Option.bind node mk_error in
  let pp = pp ~pp_format in
  Lsp.JFleche.GoalsAnswer.(
    to_yojson pp
      { textDocument; position; range; goals; program; messages; error })
  |> Result.ok

let goals ~pp_format ~mode ~pretac () ~token ~doc ~point =
  let lines = Fleche.Doc.lines doc in
  let f () = goals ~pp_format ~mode ~pretac () ~token ~doc ~point in
  Request.R.of_execution ~lines ~name:"goals" ~f ()
