(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(** This is the platform-independent code for the implementation of the Flèche
    LSP interface, BEWARE of deps, this must be able to run in a Web Worker
    context *)

module F = Format
module J = Yojson.Safe
module U = Yojson.Safe.Util

let field name dict = List.(assoc name dict)
let int_field name dict = U.to_int (field name dict)
let dict_field name dict = U.to_assoc (field name dict)
let list_field name dict = U.to_list (field name dict)
let string_field name dict = U.to_string (field name dict)

module LIO = Lsp.Io
module LSP = Lsp.Base

(** LSP loop internal state: mainly the data needed to create a new document. In
    particular, we need:

    - the core root state of Coq
    - the list of workspaces configured

    Our notion of workspace corresponds to the usual notion in Coq of "theory",
    (that is to say, a [_CoqProject] or [(coq.theory ...)] declaration), which
    is to say a set of files that share a common logical path and logical
    mappings to other theories.

    [_CoqProject]-based workspaces need an explicit global flag setup, whereas
    dune-based ones declare dependencies on other workspaces. *)
module State = struct
  type t =
    { cmdline : Coq.Workspace.CmdLine.t
    ; root_state : Coq.State.t
    ; workspaces : (string * Coq.Workspace.t) list
    }

  open Lsp.Workspace

  let add_workspace state { WorkspaceFolder.uri; _ } =
    let dir = Lang.LUri.File.to_string_file uri in
    let { cmdline; workspaces; _ } = state in
    let ws = Coq.Workspace.guess ~debug:false ~cmdline ~dir in
    { state with workspaces = (dir, ws) :: workspaces }

  let del_workspace state { WorkspaceFolder.uri; _ } =
    let dir = Lang.LUri.File.to_string_file uri in
    { state with workspaces = List.remove_assoc dir state.workspaces }

  let is_in_dir ~dir ~file = CString.is_prefix dir file

  let workspace_of_uri ~uri ~state =
    let { root_state; workspaces; _ } = state in
    let file = Lang.LUri.File.to_string_file uri in
    match List.find_opt (fun (dir, _) -> is_in_dir ~dir ~file) workspaces with
    | None ->
      LIO.logMessage ~lvl:1 ~message:"file not in workspace";
      (root_state, snd (List.hd workspaces))
    | Some (_, workspace) -> (root_state, workspace)
end

let do_changeWorkspaceFolders ~ofn:_ ~state params =
  let open Lsp.Workspace in
  let { DidChangeWorkspaceFoldersParams.event } =
    DidChangeWorkspaceFoldersParams.of_yojson (`Assoc params) |> Result.get_ok
  in
  let { WorkspaceFoldersChangeEvent.added; removed } = event in
  let state = List.fold_left State.add_workspace state added in
  let state = List.fold_left State.del_workspace state removed in
  state

module PendingRequest = struct
  type t =
    | DocRequest of
        { uri : Lang.LUri.File.t
        ; handler : Request.document
        }
    | PosRequest of
        { uri : Lang.LUri.File.t
        ; point : int * int
        ; handler : Request.position
        }

  (* Debug printing *)
  let data fmt = function
    | DocRequest { uri = _; handler = _ } -> Format.fprintf fmt "{k:doc}"
    | PosRequest { uri = _; point; handler = _ } ->
      Format.fprintf fmt "{k:pos | l: %d, c: %d}" (fst point) (snd point)

  let postpone ~id pr =
    match pr with
    | DocRequest { uri; _ } -> Doc_manager.add_on_completion ~uri ~id
    | PosRequest { uri; point; _ } -> Doc_manager.add_on_point ~uri ~id ~point

  let cancel ~id pr =
    match pr with
    | DocRequest { uri; _ } -> Doc_manager.remove_on_completion ~uri ~id
    | PosRequest { uri; point; _ } ->
      Doc_manager.remove_on_point ~uri ~id ~point

  let serve pr =
    match pr with
    | DocRequest { uri; handler } ->
      let doc = Doc_manager.find_doc ~uri in
      handler ~doc
    | PosRequest { uri; point; handler } ->
      let doc = Doc_manager.find_doc ~uri in
      handler ~point ~doc
end

(* main module with [answer, postpone, cancel, serve] methods *)
module Rq = struct
  (* Answer a request *)
  let answer ~ofn ~id result =
    (match result with
    | Result.Ok result -> LSP.mk_reply ~id ~result
    | Error (code, message) -> LSP.mk_request_error ~id ~code ~message)
    |> ofn

  (* private to the Rq module *)
  let _rtable : (int, PendingRequest.t) Hashtbl.t = Hashtbl.create 673

  let postpone ~id (pr : PendingRequest.t) =
    if Fleche.Debug.request_delay then
      LIO.trace "request" ("postponing rq : " ^ string_of_int id);
    PendingRequest.postpone ~id pr;
    Hashtbl.add _rtable id pr

  (* Consumes a request, if alive, it answers mandatorily *)
  let consume_ ~ofn ~f id =
    match Hashtbl.find_opt _rtable id with
    | Some pr ->
      Hashtbl.remove _rtable id;
      f pr |> answer ~ofn ~id
    | None ->
      LIO.trace "can't consume cancelled request: " (string_of_int id);
      ()

  let cancel ~ofn ~code ~message id : unit =
    (* fail the request, do cleanup first *)
    let f pr =
      let () = PendingRequest.cancel ~id pr in
      Error (code, message)
    in
    consume_ ~ofn ~f id

  let debug_serve id pr =
    if Fleche.Debug.request_delay then
      LIO.trace "serving"
        (Format.asprintf "rq: %d | %a" id PendingRequest.data pr)

  let serve ~ofn id =
    let f pr =
      debug_serve id pr;
      PendingRequest.serve pr
    in
    consume_ ~ofn ~f id
end

module RAction = struct
  type t =
    | ServeNow of Request.R.t
    | Postpone of PendingRequest.t

  let now r = ServeNow r
  let error (code, msg) = ServeNow (Error (code, msg))
end

let action_request ~ofn ~id action =
  match action with
  | RAction.ServeNow r -> Rq.answer ~ofn ~id r
  | RAction.Postpone p -> Rq.postpone ~id p

let serve_postponed_requests ~ofn rl = Int.Set.iter (Rq.serve ~ofn) rl

(***********************************************************************)
(* Start of protocol handlers *)

(* helpers; fix to have better errors on wrong protocol code *)
let get_uri params =
  let document =
    field "textDocument" params
    |> Lsp.Doc.TextDocumentIdentifier.of_yojson |> Result.get_ok
  in
  let Lsp.Doc.TextDocumentIdentifier.{ uri } = document in
  uri

let get_uri_oversion params =
  let document =
    field "textDocument" params
    |> Lsp.Doc.OVersionedTextDocumentIdentifier.of_yojson |> Result.get_ok
  in
  let Lsp.Doc.OVersionedTextDocumentIdentifier.{ uri; version } = document in
  (uri, version)

let get_uri_version params =
  let document =
    field "textDocument" params
    |> Lsp.Doc.VersionedTextDocumentIdentifier.of_yojson |> Result.get_ok
  in
  let Lsp.Doc.VersionedTextDocumentIdentifier.{ uri; version } = document in
  (uri, version)

let do_shutdown = RAction.now (Ok `Null)

let do_open ~ofn ~(state : State.t) params =
  let document =
    field "textDocument" params
    |> Lsp.Doc.TextDocumentItem.of_yojson |> Result.get_ok
  in
  let Lsp.Doc.TextDocumentItem.{ uri; version; text; _ } = document in
  let root_state, workspace = State.workspace_of_uri ~uri ~state in
  Doc_manager.create ~ofn ~root_state ~workspace ~uri ~raw:text ~version

let do_change ~ofn params =
  let uri, version = get_uri_version params in
  let changes = List.map U.to_assoc @@ list_field "contentChanges" params in
  match changes with
  | [] ->
    LIO.trace "do_change" "no change in changes? ignoring";
    ()
  | _ :: _ :: _ ->
    LIO.trace "do_change"
      "more than one change unsupported due to sync method, ignoring";
    ()
  | change :: _ ->
    let raw = string_field "text" change in
    let invalid_rq = Doc_manager.change ~ofn ~uri ~version ~raw in
    let code = -32802 in
    let message = "Request got old in server" in
    Int.Set.iter (Rq.cancel ~ofn ~code ~message) invalid_rq

let do_close ~ofn:_ params =
  let uri = get_uri params in
  Doc_manager.close ~uri

let get_textDocument params =
  let uri = get_uri params in
  let doc = Doc_manager.find_doc ~uri in
  (uri, doc)

let get_textOVersionDocument params =
  let uri, version = get_uri_oversion params in
  let doc = Doc_manager.find_doc ~uri in
  (uri, version, doc)

let get_position params =
  let pos = dict_field "position" params in
  let line, character = (int_field "line" pos, int_field "character" pos) in
  (line, character)

let request_in_range ~(doc : Fleche.Doc.t) ~version (line, col) =
  (* EJGA: I'd be nice to better share the code between postponement here and
     request wake-up in [Doc_manager] (note how both call [Target.reached] *)
  let in_range =
    match doc.completed with
    | Yes _ -> true
    | Failed range | FailedPermanent range | Stopped range ->
      Fleche.Doc.Target.reached ~range (line, col)
  in
  let in_range =
    match version with
    | None -> in_range
    | Some version -> doc.version >= version && in_range
  in
  in_range

let do_position_request ~postpone ~params ~handler =
  let uri, version, doc = get_textOVersionDocument params in
  let point = get_position params in
  let in_range = request_in_range ~doc ~version point in
  match (in_range, postpone) with
  | true, _ -> RAction.now (handler ~doc ~point)
  | false, true -> Postpone (PosRequest { uri; point; handler })
  | false, false ->
    let code = -32802 in
    let message = "Document is not ready" in
    RAction.error (code, message)

let do_hover = do_position_request ~postpone:false ~handler:Rq_hover.hover
let do_goals = do_position_request ~postpone:true ~handler:Rq_goals.goals

let do_definition =
  do_position_request ~postpone:true ~handler:Rq_definition.request

let do_completion =
  do_position_request ~postpone:true ~handler:Rq_completion.completion

(* Requires the full document to be processed *)
let do_document_request ~params ~handler =
  let uri, doc = get_textDocument params in
  match doc.completed with
  | Yes _ -> RAction.now (handler ~doc)
  | Stopped _ | Failed _ | FailedPermanent _ ->
    Postpone (PendingRequest.DocRequest { uri; handler })

let do_symbols = do_document_request ~handler:Rq_symbols.symbols
let do_document = do_document_request ~handler:Rq_document.request
let do_save_vo = do_document_request ~handler:Rq_save.request
let do_lens = do_document_request ~handler:Rq_lens.request

let do_trace params =
  let trace = string_field "value" params in
  match LIO.TraceValue.of_string trace with
  | Ok t -> LIO.set_trace_value t
  | Error e -> LIO.trace "trace" ("invalid value: " ^ e)

let do_cancel ~ofn ~params =
  let id = int_field "id" params in
  let code = -32800 in
  let message = "Cancelled by client" in
  Rq.cancel ~ofn ~code ~message id

(***********************************************************************)

(** LSP Init routine *)
exception Lsp_exit

let log_workspace (dir, w) =
  let message, extra = Coq.Workspace.describe w in
  LIO.trace "workspace" ("initialized " ^ dir) ~extra;
  LIO.logMessage ~lvl:3 ~message

let version () =
  let dev_version =
    match Build_info.V1.version () with
    | None -> "N/A"
    | Some bi -> Build_info.V1.Version.to_string bi
  in
  Format.asprintf "version %s, dev: %s, Coq version: %s, OS: %s" Version.server
    dev_version Coq_config.version Sys.os_type

module Init_effect = struct
  type t =
    | Success of (string * Coq.Workspace.t) list
    | Loop
    | Exit
end

let lsp_init_process ~ofn ~cmdline ~debug msg : Init_effect.t =
  match msg with
  | LSP.Message.Request { method_ = "initialize"; id; params } ->
    (* At this point logging is allowed per LSP spec *)
    let message =
      Format.asprintf "Initializing coq-lsp server %s" (version ())
    in
    LIO.logMessage ~lvl:3 ~message;
    let result, dirs = Rq_init.do_initialize ~params in
    Rq.answer ~ofn ~id (Result.ok result);
    LIO.logMessage ~lvl:3 ~message:"Server initialized";
    (* Workspace initialization *)
    let debug = debug || !Fleche.Config.v.debug in
    let workspaces =
      List.map (fun dir -> (dir, Coq.Workspace.guess ~cmdline ~debug ~dir)) dirs
    in
    List.iter log_workspace workspaces;
    Success workspaces
  | LSP.Message.Request { id; _ } ->
    (* per spec *)
    LSP.mk_request_error ~id ~code:(-32002) ~message:"server not initialized"
    |> ofn;
    Loop
  | LSP.Message.Notification { method_ = "exit"; params = _ } -> Exit
  | LSP.Message.Notification _ ->
    (* We can't log before getting the initialize message *)
    Loop

(** Dispatching *)
let dispatch_notification ~ofn ~state ~method_ ~params : unit =
  match method_ with
  (* Lifecycle *)
  | "exit" -> raise Lsp_exit
  (* setTrace *)
  | "$/setTrace" -> do_trace params
  (* Document lifetime *)
  | "textDocument/didOpen" -> do_open ~ofn ~state params
  | "textDocument/didChange" -> do_change ~ofn params
  | "textDocument/didClose" -> do_close ~ofn params
  | "textDocument/didSave" -> Cache.save_to_disk ()
  (* Workspace *)
  | "workspace/didChangeWorkspaceFolders" -> () (* XXX *)
  (* Cancel Request *)
  | "$/cancelRequest" -> do_cancel ~ofn ~params
  (* NOOPs *)
  | "initialized" -> ()
  (* Generic handler *)
  | msg -> LIO.trace "no_handler" msg

let dispatch_state_notification ~ofn ~state ~method_ ~params : State.t =
  match method_ with
  (* Workspace *)
  | "workspace/didChangeWorkspaceFolders" ->
    do_changeWorkspaceFolders ~ofn ~state params
  | _ ->
    dispatch_notification ~ofn ~state ~method_ ~params;
    state

let dispatch_request ~method_ ~params : RAction.t =
  match method_ with
  (* Lifecyle *)
  | "initialize" ->
    LIO.trace "dispatch_request" "duplicate initialize request! Rejecting";
    (* XXX what's the error code here *)
    RAction.error (-32600, "Invalid Request: server already initialized")
  | "shutdown" -> do_shutdown
  (* Symbols and info about the document *)
  | "textDocument/completion" -> do_completion ~params
  | "textDocument/definition" -> do_definition ~params
  | "textDocument/documentSymbol" -> do_symbols ~params
  | "textDocument/hover" -> do_hover ~params
  | "textDocument/codeLens" -> do_lens ~params
  (* Proof-specific stuff *)
  | "proof/goals" -> do_goals ~params
  (* Proof-specific stuff *)
  | "coq/saveVo" -> do_save_vo ~params
  (* Coq specific stuff *)
  | "coq/getDocument" -> do_document ~params
  (* Generic handler *)
  | msg ->
    LIO.trace "no_handler" msg;
    RAction.error (-32601, "method not found")

let dispatch_request ~ofn ~id ~method_ ~params =
  dispatch_request ~method_ ~params |> action_request ~ofn ~id

let dispatch_request ~ofn ~id ~method_ ~params =
  try dispatch_request ~ofn ~id ~method_ ~params
  with Doc_manager.AbortRequest ->
    (* -32603 = internal error *)
    let code = -32603 in
    let message = "Internal Document Request Queue Error" in
    Rq.cancel ~ofn ~code ~message id

let dispatch_message ~ofn ~state (com : LSP.Message.t) : State.t =
  match com with
  | Notification { method_; params } ->
    dispatch_state_notification ~ofn ~state ~method_ ~params
  | Request { id; method_; params } ->
    dispatch_request ~ofn ~id ~method_ ~params;
    state

(* Queue handling *)

(***********************************************************************)
(* The queue strategy is: we keep pending document checks in Doc_manager, they
   are only resumed when the rest of requests in the queue are served.

   Note that we should add a method to detect stale requests; maybe cancel them
   when a new edit comes. *)

type 'a cont =
  | Cont of 'a
  | Yield of 'a

let check_or_yield ~ofn ~state =
  match Doc_manager.Check.maybe_check ~ofn with
  | None -> Yield state
  | Some ready ->
    let () = serve_postponed_requests ~ofn ready in
    Cont state

let request_queue = Queue.create ()

let dispatch_or_resume_check ~ofn ~state =
  match Queue.peek_opt request_queue with
  | None ->
    (* This is where we make progress on document checking; kind of IDLE
       workqueue. *)
    Control.interrupt := false;
    check_or_yield ~ofn ~state
  | Some com ->
    (* TODO: optimize the queue? EJGA: I've found that VS Code as a client keeps
       the queue tidy by itself, so this works fine as now *)
    ignore (Queue.pop request_queue);
    LIO.trace "process_queue" ("Serving Request: " ^ LSP.Message.method_ com);
    (* We let Coq work normally now *)
    Control.interrupt := false;
    Cont (dispatch_message ~ofn ~state com)

(* Wrapper for the top-level call *)
let dispatch_or_resume_check ~ofn ~state =
  try Some (dispatch_or_resume_check ~ofn ~state) with
  | U.Type_error (msg, obj) ->
    LIO.trace_object msg obj;
    Some (Yield state)
  | Lsp_exit ->
    (* EJGA: Maybe remove Lsp_exit and have dispatch_or_resume_check return an
       action? *)
    None
  | exn ->
    (* Note: We should never arrive here from Coq, as every call to Coq should
       be wrapper in Coq.Protect. So hitting this codepath, is effectively a
       coq-lsp internal error and should be fixed *)
    let bt = Printexc.get_backtrace () in
    let iexn = Exninfo.capture exn in
    LIO.trace "process_queue"
      (if Printexc.backtrace_status () then "bt=true" else "bt=false");
    (* let method_name = LSP.Message.method_ com in *)
    (* LIO.trace "process_queue" ("exn in method: " ^ method_name); *)
    LIO.trace "print_exn [OCaml]" (Printexc.to_string exn);
    LIO.trace "print_exn [Coq  ]" Pp.(string_of_ppcmds CErrors.(iprint iexn));
    LIO.trace "print_bt  [OCaml]" bt;
    Some (Yield state)

let enqueue_message (com : LSP.Message.t) =
  if Fleche.Debug.sched_wakeup then
    LIO.trace "-> enqueue" (Format.asprintf "%.2f" (Unix.gettimeofday ()));
  (* TODO: this is the place to cancel pending requests that are invalid, and in
     general, to perform queue optimizations *)
  Queue.push com request_queue;
  Control.interrupt := true
