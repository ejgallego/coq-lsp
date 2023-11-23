(************************************************************************)
(* Coq Language Server Protocol -- Requests                             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(* Replace by ppx when we can print goals properly in the client *)
let mk_message (range, level, text) =
  let level = Lang.Diagnostic.Severity.to_int level in
  Lsp.JFleche.Message.{ range; level; text }

let mk_messages node =
  Option.map Fleche.Doc.Node.messages node
  |> Option.cata (List.map mk_message) []

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

let parse ~loc tac st =
  let str = Gramlib.Stream.of_string tac in
  let str = Coq.Parsing.Parsable.make ?loc str in
  Coq.Parsing.parse ~st str

let parse_and_execute_in ~loc tac st =
  let open Coq.Protect.E.O in
  let* ast = parse ~loc tac st in
  match ast with
  | Some ast -> (Fleche.Memo.Interp.eval (st, ast)).res
  (* On EOF we return the previous state, the command was the empty string or a
     comment *)
  | None -> Coq.Protect.E.ok st

let run_pretac ~loc ~st pretac =
  match pretac with
  | None -> Coq.Protect.E.ok st
  | Some tac -> Coq.State.in_stateM ~st ~f:(parse_and_execute_in ~loc tac) st

let get_goal_info ~doc ~point ~mode ~pretac () =
  let open Fleche in
  let node = Info.LC.node ~doc ~point mode in
  match node with
  | None -> Coq.Protect.E.ok (None, None)
  | Some node ->
    let open Coq.Protect.E.O in
    let st = Doc.Node.state node in
    (* XXX: Get the location from node *)
    let loc = None in
    let* st = run_pretac ~loc ~st pretac in
    let+ goals = Info.Goals.goals ~st in
    let program = Info.Goals.program ~st in
    (goals, Some program)

let goals ~pp_format ~mode ~pretac () ~doc ~point =
  let open Fleche in
  let uri, version = (doc.Doc.uri, doc.version) in
  let textDocument = Lsp.Doc.VersionedTextDocumentIdentifier.{ uri; version } in
  let position =
    Lang.Point.{ line = fst point; character = snd point; offset = -1 }
  in
  let open Coq.Protect.E.O in
  let+ goals, program = get_goal_info ~doc ~point ~mode ~pretac () in
  let node = Info.LC.node ~doc ~point Exact in
  let messages = mk_messages node in
  let error = Option.bind node mk_error in
  let pp = pp ~pp_format in
  Lsp.JFleche.GoalsAnswer.(
    to_yojson pp { textDocument; position; goals; program; messages; error })
  |> Result.ok

let goals ~pp_format ~mode ~pretac () ~doc ~point =
  let f () = goals ~pp_format ~mode ~pretac () ~doc ~point in
  Request.R.of_execution ~name:"goals" ~f ()
