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
  | Box

(* BoxLayout helpers *)
let set_flag flag value f =
  let v = !flag in
  flag := value;
  try
    let res = f () in
    flag := v;
    res
  with exn ->
    flag := v;
    raise exn

let layout_term env sigma t =
  (* Coq stores goals in kernel-format, we need to recover the AST back before
     calling the layout engine; this is called "externalization" in Coq
     jargon *)
  let t = Constrextern.extern_type env sigma t in
  let html = Layout.(Term.layout env sigma t |> BoxModel.Render.to_html) in
  Format.asprintf "@[%a@]" (Tyxml.Html.pp_elt ()) html

let layout_term env sigma t =
  set_flag
    (* Notations = no *)
    (* Constrextern.print_no_symbol true *)
    (* Notations = yes *)
    Constrextern.print_no_symbol false (fun () -> layout_term env sigma t)

let pp ~pp_format ~token env evd x =
  match pp_format with
  | Pp -> Fleche.Info.Goals.to_pp ~token env evd x |> Lsp.JCoq.Pp.to_yojson
  | Str ->
    let pp = Fleche.Info.Goals.to_pp ~token env evd x in
    `String (Pp.string_of_ppcmds pp)
  | Box ->
    let pp = layout_term env evd x in
    `List [ `String "box"; `String pp ]

let run_pretac ~token ~loc ~st pretac =
  match pretac with
  | None -> Coq.Protect.E.ok st
  | Some tac -> Fleche.Doc.run ~token ?loc ~st tac

let get_goal_info ~pp_format ~token ~doc ~point ~mode ~pretac () =
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
    let pr = pp ~pp_format in
    let+ goals = Info.Goals.goals ~token ~pr ~st in
    let program = Info.Goals.program ~st in
    (goals, Some program)

let get_node_info ~doc ~point ~mode =
  let open Fleche in
  let mode =
    if !Fleche.Config.v.messages_follow_goal then mode else Info.Exact
  in
  let node = Info.LC.node ~doc ~point mode in
  let range = Option.map Doc.Node.range node in
  let messages = mk_messages node in
  let error = Option.bind node mk_error in
  (range, messages, error)

let goals ~pp_format ~mode ~pretac () ~token ~doc ~point =
  let open Fleche in
  let uri, version = (doc.Doc.uri, doc.version) in
  let textDocument = Lsp.Doc.VersionedTextDocumentIdentifier.{ uri; version } in
  let position =
    Lang.Point.{ line = fst point; character = snd point; offset = -1 }
  in
  let open Coq.Protect.E.O in
  let+ goals, program =
    get_goal_info ~pp_format ~token ~doc ~point ~mode ~pretac ()
  in
  let range, messages, error = get_node_info ~doc ~point ~mode in
  Lsp.JFleche.GoalsAnswer.(
    to_yojson
      (fun x -> x)
      (fun x -> Lsp.JCoq.Pp.to_yojson x)
      { textDocument; position; range; goals; program; messages; error })
  |> Result.ok

let goals ~pp_format ~mode ~pretac () ~token ~doc ~point =
  let lines = Fleche.Doc.lines doc in
  let f () = goals ~pp_format ~mode ~pretac () ~token ~doc ~point in
  Request.R.of_execution ~lines ~name:"goals" ~f ()
