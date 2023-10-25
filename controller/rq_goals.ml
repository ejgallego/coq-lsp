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

(* XXX: Speculative execution here requires more thought, about errors,
   location, we need to make the request fail if it is not good, etc... Moreover
   we should tune whether we cache the results; we try this for now. *)
let parse_and_execute_in tac st =
  (* Parse tac, loc==FIXME *)
  let str = Gramlib.Stream.of_string tac in
  let str = Coq.Parsing.Parsable.make ?loc:None str in
  match Coq.Parsing.parse ~st str with
  | Coq.Protect.E.{ r = Interrupted; feedback = _ }
  | Coq.Protect.E.{ r = Completed (Error _); feedback = _ }
  | Coq.Protect.E.{ r = Completed (Ok None); feedback = _ } -> None
  | Coq.Protect.E.{ r = Completed (Ok (Some ast)); feedback = _ } -> (
    let open Fleche.Memo in
    (* XXX use the bind in Coq.Protect.E *)
    match (Interp.eval (st, ast)).res with
    | Coq.Protect.E.{ r = Interrupted; feedback = _ }
    | Coq.Protect.E.{ r = Completed (Error _); feedback = _ } -> None
    | Coq.Protect.E.{ r = Completed (Ok st); feedback = _ } -> Some st)

let run_pretac ?pretac st =
  match pretac with
  | None ->
    (* Debug option *)
    (* Lsp.Io.trace "goals" "pretac empty"; *)
    Some st
  | Some tac -> Fleche.Info.in_state ~st ~f:(parse_and_execute_in tac) st

let get_goal_info ~doc ~point ?pretac () =
  let open Fleche in
  let goals_mode = get_goals_mode () in
  let node = Info.LC.node ~doc ~point goals_mode in
  match node with
  | None -> (None, None)
  | Some node -> (
    match run_pretac ?pretac node.Doc.Node.state with
    | None -> (None, None)
    | Some st ->
      let goals = Info.Goals.goals ~st in
      let program = Info.Goals.program ~st in
      (goals, Some program))

let goals ~pp_format ?pretac () ~doc ~point =
  let open Fleche in
  let uri, version = (doc.Doc.uri, doc.version) in
  let textDocument = Lsp.Doc.VersionedTextDocumentIdentifier.{ uri; version } in
  let position =
    Lang.Point.{ line = fst point; character = snd point; offset = -1 }
  in
  let goals, program = get_goal_info ~doc ~point ?pretac () in
  let node = Info.LC.node ~doc ~point Exact in
  let messages = mk_messages node in
  let error = Option.bind node mk_error in
  let pp = pp ~pp_format in
  Lsp.JFleche.GoalsAnswer.(
    to_yojson pp { textDocument; position; goals; program; messages; error })
  |> Result.ok
