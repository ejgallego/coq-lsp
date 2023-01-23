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

module F = Format
module J = Yojson.Safe
module U = Yojson.Safe.Util

let int_field name dict = U.to_int List.(assoc name dict)
let dict_field name dict = U.to_assoc List.(assoc name dict)
let list_field name dict = U.to_list List.(assoc name dict)
let string_field name dict = U.to_string List.(assoc name dict)

(* Conditionals *)
let option_cata f d x =
  match x with
  | None -> d
  | Some x -> f x

let option_default x d =
  match x with
  | None -> d
  | Some x -> x

let ostring_field name dict = Option.map U.to_string (List.assoc_opt name dict)
let oint_field name dict = Option.map U.to_int (List.assoc_opt name dict)

let odict_field name dict =
  option_default
    U.(to_option to_assoc (option_default List.(assoc_opt name dict) `Null))
    []

(* LSP loop internal state, mainly the stuff needed to create a new document.
   Note that we could [apply] [workspace] to the root_state, but for now we keep
   the flexibility for a server to work with different workspaces. *)
module State = struct
  type t =
    { root_state : Coq.State.t
    ; workspace : Coq.Workspace.t
    }
end

module LIO = Lsp.Io
module LSP = Lsp.Base
module Check = Doc_manager.Check

module PendingRequest = struct
  type t =
    | DocRequest of
        { uri : string
        ; handler : Requests.document_request
        }
    | PosRequest of
        { uri : string
        ; point : int * int
        ; handler : Requests.position_request
        }

  let data fmt = function
    | DocRequest { uri = _; handler = _ } -> Format.fprintf fmt "{k:doc}"
    | PosRequest { uri = _; point; handler = _ } ->
      Format.fprintf fmt "{k:pos | l: %d, c: %d}" (fst point) (snd point)

  let postpone ~id pr =
    match pr with
    | DocRequest { uri; _ } -> Doc_manager.add_on_completion ~uri ~id
    | PosRequest { uri; point; _ } -> Doc_manager.add_on_point ~uri ~id ~point
end

module RAction = struct
  type t =
    | ServeNow of (Yojson.Safe.t, int * string) Result.t
    | Postpone of PendingRequest.t

  let ok r = ServeNow (Ok r)
  let error (code, msg) = ServeNow (Error (code, msg))
end

(* Request Handling: The client expects a reply *)
module CoqLspOption = struct
  type t = [%import: Fleche.Config.t] [@@deriving yojson]
end

let do_client_options coq_lsp_options : unit =
  LIO.trace "init" "custom client options:";
  LIO.trace_object "init" (`Assoc coq_lsp_options);
  match CoqLspOption.of_yojson (`Assoc coq_lsp_options) with
  | Ok v -> Fleche.Config.v := v
  | Error msg -> LIO.trace "CoqLspOption.of_yojson error: " msg

let check_client_version client_version : unit =
  LIO.trace "client_version" client_version;
  if String.(equal client_version "any" || equal client_version Version.server)
  then () (* Version OK *)
  else
    let message =
      Format.asprintf "Incorrect client version: %s , expected %s."
        client_version Version.server
    in
    LIO.logMessage ~lvl:1 ~message

let do_initialize ~params =
  let trace =
    ostring_field "trace" params
    |> option_cata LIO.TraceValue.of_string LIO.TraceValue.Off
  in
  LIO.set_trace_value trace;
  let coq_lsp_options = odict_field "initializationOptions" params in
  do_client_options coq_lsp_options;
  check_client_version !Fleche.Config.v.client_version;
  let client_capabilities = odict_field "capabilities" params in
  if Fleche.Debug.lsp_init then (
    LIO.trace "init" "client capabilities:";
    LIO.trace_object "init" (`Assoc client_capabilities));
  let capabilities =
    [ ("textDocumentSync", `Int 1)
    ; ("documentSymbolProvider", `Bool true)
    ; ("hoverProvider", `Bool true)
    ; ("completionProvider", `Assoc [])
    ; ("codeActionProvider", `Bool false)
    ]
  in
  `Assoc
    [ ("capabilities", `Assoc capabilities)
    ; ( "serverInfo"
      , `Assoc
          [ ("name", `String "coq-lsp (C) Inria 2022-2023")
          ; ("version", `String Version.server)
          ] )
    ]
  |> Result.ok

let rtable : (int, PendingRequest.t) Hashtbl.t = Hashtbl.create 673

let answer_request ~ofmt ~id result =
  (match result with
  | Result.Ok result -> LSP.mk_reply ~id ~result
  | Error (code, message) -> LSP.mk_request_error ~id ~code ~message)
  |> LIO.send_json ofmt

let postpone_request ~id (pr : PendingRequest.t) =
  if Fleche.Debug.request_delay then
    LIO.trace "request" ("postponing rq : " ^ string_of_int id);
  PendingRequest.postpone ~id pr;
  Hashtbl.add rtable id pr

let action_request ~ofmt ~id action =
  match action with
  | RAction.ServeNow r -> answer_request ~ofmt ~id r
  | RAction.Postpone p -> postpone_request ~id p

let cancel_rq ~ofmt ~code ~message id =
  match Hashtbl.find_opt rtable id with
  | None ->
    (* Request already served or cancelled *)
    ()
  | Some _ ->
    Hashtbl.remove rtable id;
    answer_request ~ofmt ~id (Error (code, message))

let do_shutdown ~params:_ = RAction.ok `Null

let do_open ~state params =
  let document = dict_field "textDocument" params in
  let uri, version, contents =
    ( string_field "uri" document
    , int_field "version" document
    , string_field "text" document )
  in
  let root_state, workspace = State.(state.root_state, state.workspace) in
  Doc_manager.create ~root_state ~workspace ~uri ~contents ~version

let do_change ~ofmt params =
  let document = dict_field "textDocument" params in
  let uri, version =
    (string_field "uri" document, int_field "version" document)
  in
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
    let contents = string_field "text" change in
    let invalid_rq = Doc_manager.change ~uri ~version ~contents in
    let code = -32802 in
    let message = "Request got old in server" in
    Int.Set.iter (cancel_rq ~ofmt ~code ~message) invalid_rq

let do_close ~ofmt:_ params =
  let document = dict_field "textDocument" params in
  let uri = string_field "uri" document in
  Doc_manager.close ~uri

let get_textDocument params =
  let document = dict_field "textDocument" params in
  let uri = string_field "uri" document in
  let doc = Doc_manager.find_doc ~uri in
  (uri, doc)

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
    | Failed range | Stopped range ->
      Fleche.Doc.Target.reached ~range (line, col)
  in
  let in_range =
    match version with
    | None -> in_range
    | Some version -> doc.version >= version && in_range
  in
  in_range

let do_position_request ~postpone ~params ~handler =
  let uri, doc = get_textDocument params in
  let version = dict_field "textDocument" params |> oint_field "version" in
  let point = get_position params in
  let in_range = request_in_range ~doc ~version point in
  match (in_range, postpone) with
  | true, _ -> RAction.ok (handler ~doc ~point)
  | false, true -> Postpone (PosRequest { uri; point; handler })
  | false, false ->
    let code = -32802 in
    let message = "Document is not ready" in
    RAction.error (code, message)

let do_hover = do_position_request ~postpone:false ~handler:Requests.hover
let do_goals = do_position_request ~postpone:true ~handler:Requests.goals

let do_completion =
  do_position_request ~postpone:true ~handler:Requests.completion

(* Requires the full document to be processed *)
let do_document_request ~params ~handler =
  let uri, doc = get_textDocument params in
  let lines = doc.contents.lines in
  match doc.completed with
  | Yes _ -> RAction.ok (handler ~lines ~doc)
  | Stopped _ | Failed _ ->
    Postpone (PendingRequest.DocRequest { uri; handler })

let do_symbols = do_document_request ~handler:Requests.symbols

let do_trace params =
  let trace = string_field "value" params in
  LIO.set_trace_value (LIO.TraceValue.of_string trace)

(***********************************************************************)

(** Misc helpers *)
let rec read_request ic =
  let com = LIO.read_request ic in
  if Fleche.Debug.read then LIO.trace_object "read" com;
  match LSP.Message.from_yojson com with
  | Ok msg -> msg
  | Error msg ->
    LIO.trace "read_request" ("error: " ^ msg);
    read_request ic

let do_cancel ~ofmt ~params =
  let id = int_field "id" params in
  let code = -32800 in
  let message = "Cancelled by client" in
  cancel_rq ~ofmt ~code ~message id

let serve_postponed ~id pr =
  if Fleche.Debug.request_delay then
    LIO.trace "[wake up]"
      (Format.asprintf "rq: %d | %a" id PendingRequest.data pr);
  match pr with
  | PendingRequest.DocRequest { uri; handler } ->
    let doc = Doc_manager.find_doc ~uri in
    let lines = doc.contents.lines in
    Some (Result.ok (handler ~lines ~doc))
  | PosRequest { uri; point; handler } ->
    let doc = Doc_manager.find_doc ~uri in
    Some (Result.ok (handler ~point ~doc))

let serve_postponed_request id =
  match Hashtbl.find_opt rtable id with
  | None ->
    LIO.trace "can't wake up cancelled request: " (string_of_int id);
    None
  | Some pr ->
    Hashtbl.remove rtable id;
    serve_postponed ~id pr

let serve_postponed_request ~ofmt id =
  serve_postponed_request id |> Option.iter (answer_request ~ofmt ~id)

let serve_postponed_requests ~ofmt rl =
  Int.Set.iter (serve_postponed_request ~ofmt) rl

(***********************************************************************)

(** LSP Init routine *)
exception Lsp_exit

let log_workspace w =
  let message, extra = Coq.Workspace.describe w in
  LIO.trace "workspace" "initialized" ~extra;
  LIO.logMessage ~lvl:3 ~message

let rec lsp_init_loop ic ofmt ~cmdline : Coq.Workspace.t =
  match read_request ic with
  | LSP.Message.Request { method_ = "initialize"; id; params } ->
    (* At this point logging is allowed per LSP spec *)
    LIO.logMessage ~lvl:3 ~message:"Initializing server";
    let result = do_initialize ~params in
    answer_request ~ofmt ~id result;
    LIO.logMessage ~lvl:3 ~message:"Server initialized";
    (* Workspace initialization *)
    let workspace = Coq.Workspace.guess ~cmdline in
    log_workspace workspace;
    workspace
  | LSP.Message.Request { id; _ } ->
    (* per spec *)
    LSP.mk_request_error ~id ~code:(-32002) ~message:"server not initialized"
    |> LIO.send_json ofmt;
    lsp_init_loop ic ofmt ~cmdline
  | LSP.Message.Notification { method_ = "exit"; params = _ } -> raise Lsp_exit
  | LSP.Message.Notification _ ->
    (* We can't log before getting the initialize message *)
    lsp_init_loop ic ofmt ~cmdline

(** Dispatching *)
let dispatch_notification ofmt ~state ~method_ ~params : unit =
  match method_ with
  (* Lifecycle *)
  | "exit" -> raise Lsp_exit
  (* setTrace *)
  | "$/setTrace" -> do_trace params
  (* Document lifetime *)
  | "textDocument/didOpen" -> do_open ~state params
  | "textDocument/didChange" -> do_change ~ofmt params
  | "textDocument/didClose" -> do_close ~ofmt params
  | "textDocument/didSave" -> Cache.save_to_disk ()
  (* Cancel Request *)
  | "$/cancelRequest" -> do_cancel ~ofmt ~params
  (* NOOPs *)
  | "initialized" -> ()
  (* Generic handler *)
  | msg -> LIO.trace "no_handler" msg

let dispatch_request ~method_ ~params : RAction.t =
  match method_ with
  (* Lifecyle *)
  | "initialize" ->
    LIO.trace "dispatch_request" "duplicate initialize request! Rejecting";
    (* XXX what's the error code here *)
    RAction.error (-32600, "Invalid Request: server already initialized")
  | "shutdown" -> do_shutdown ~params
  (* Symbols and info about the document *)
  | "textDocument/completion" -> do_completion ~params
  | "textDocument/documentSymbol" -> do_symbols ~params
  | "textDocument/hover" -> do_hover ~params
  (* Proof-specific stuff *)
  | "proof/goals" -> do_goals ~params
  (* Generic handler *)
  | msg ->
    LIO.trace "no_handler" msg;
    RAction.error (-32601, "method not found")

let dispatch_request ofmt ~id ~method_ ~params =
  dispatch_request ~method_ ~params |> action_request ~ofmt ~id

let dispatch_request ofmt ~id ~method_ ~params =
  try dispatch_request ofmt ~id ~method_ ~params
  with Doc_manager.AbortRequest ->
    (* -32603 = internal error *)
    let code = -32603 in
    let message = "Internal Document Request Queue Error" in
    cancel_rq ~ofmt ~code ~message id

let dispatch_message ofmt ~state (com : LSP.Message.t) =
  match com with
  | Notification { method_; params } ->
    dispatch_notification ofmt ~state ~method_ ~params
  | Request { id; method_; params } ->
    dispatch_request ofmt ~id ~method_ ~params

(***********************************************************************)
(* The queue strategy is: we keep pending document checks in Doc_manager, they
   are only resumed when the rest of requests in the queue are served.

   Note that we should add a method to detect stale requests; maybe cancel them
   when a new edit comes. *)

(** Main event queue *)
let request_queue = Queue.create ()

let dispatch_or_resume_check ~ofmt ~state =
  match Queue.peek_opt request_queue with
  | None ->
    (* This is where we make progress on document checking; kind of IDLE
       workqueue. *)
    Control.interrupt := false;
    let ready = Check.check_or_yield ~ofmt in
    serve_postponed_requests ~ofmt ready
  | Some com ->
    (* TODO: optimize the queue? EJGA: I've found that VS Code as a client keeps
       the queue tidy by itself, so this works fine as now *)
    ignore (Queue.pop request_queue);
    LIO.trace "process_queue" ("Serving Request: " ^ LSP.Message.method_ com);
    (* We let Coq work normally now *)
    Control.interrupt := false;
    dispatch_message ofmt ~state com

(* Wrapper for the top-level call *)
let dispatch_or_resume_check ~ofmt ~state =
  try dispatch_or_resume_check ~ofmt ~state with
  | U.Type_error (msg, obj) -> LIO.trace_object msg obj
  | Lsp_exit -> raise Lsp_exit
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
    LIO.trace "print_bt  [OCaml]" bt

let rec process_queue ofmt ~state =
  if Fleche.Debug.sched_wakeup then
    LIO.trace "<- dequeue" (Format.asprintf "%.2f" (Unix.gettimeofday ()));
  dispatch_or_resume_check ~ofmt ~state;
  process_queue ofmt ~state

let process_input (com : LSP.Message.t) =
  if Fleche.Debug.sched_wakeup then
    LIO.trace "-> enqueue" (Format.asprintf "%.2f" (Unix.gettimeofday ()));
  (* TODO: this is the place to cancel pending requests that are invalid, and in
     general, to perform queue optimizations *)
  Queue.push com request_queue;
  Control.interrupt := true

(* Main loop *)
let lsp_cb =
  Fleche.Io.CallBack.
    { trace = LIO.trace
    ; send_diagnostics =
        (fun ~ofmt ~uri ~version diags ->
          Lsp_util.lsp_of_diags ~uri ~version diags |> Lsp.Io.send_json ofmt)
    ; send_fileProgress =
        (fun ~ofmt ~uri ~version progress ->
          Lsp_util.lsp_of_progress ~uri ~version progress
          |> Lsp.Io.send_json ofmt)
    }

let lvl_to_severity (lvl : Feedback.level) =
  match lvl with
  | Feedback.Debug -> 5
  | Feedback.Info -> 4
  | Feedback.Notice -> 3
  | Feedback.Warning -> 2
  | Feedback.Error -> 1

let add_message lvl loc msg q =
  let lvl = lvl_to_severity lvl in
  q := (loc, lvl, msg) :: !q

let mk_fb_handler q Feedback.{ contents; _ } =
  match contents with
  | Message (((Error | Warning | Notice) as lvl), loc, msg) ->
    add_message lvl loc msg q
  | Message ((Info as lvl), loc, msg) ->
    if !Fleche.Config.v.show_coq_info_messages then add_message lvl loc msg q
    else ()
  | Message (Debug, _loc, _msg) -> ()
  | _ -> ()

let coq_init ~fb_queue ~bt =
  let fb_handler = mk_fb_handler fb_queue in
  let debug = bt || Fleche.Debug.backtraces in
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  Coq.Init.(coq_init { fb_handler; debug; load_module; load_plugin })

let lsp_main bt coqlib vo_load_path ml_include_path =
  (* We output to stdout *)
  let ic = stdin in
  let oc = F.std_formatter in

  (* Set log channels *)
  LIO.set_log_channel oc;
  Fleche.Io.CallBack.set lsp_cb;

  (* IMPORTANT: LSP spec forbids any message from server to client before
     initialize is received *)

  (* Core Coq initialization *)
  let fb_queue = Coq.Protect.fb_queue in
  let root_state = coq_init ~fb_queue ~bt in
  let cmdline =
    { Coq.Workspace.CmdLine.coqlib; vo_load_path; ml_include_path }
  in

  (* Read JSON-RPC messages and push them to the queue *)
  let rec read_loop () =
    let msg = read_request ic in
    process_input msg;
    read_loop ()
  in

  (* Input/output will happen now *)
  try
    (* LSP Server server initialization *)
    let workspace = lsp_init_loop ic oc ~cmdline in

    (* Core LSP loop context *)
    let state = { State.root_state; workspace } in

    (* Read workspace state (noop for now) *)
    Cache.read_from_disk ();

    let (_ : Thread.t) = Thread.create (fun () -> process_queue oc ~state) () in

    read_loop ()
  with
  | (LIO.ReadError "EOF" | Lsp_exit) as exn ->
    let message =
      "server exiting"
      ^ if exn = Lsp_exit then "" else " [uncontrolled LSP shutdown]"
    in
    LIO.logMessage ~lvl:1 ~message
  | exn ->
    let bt = Printexc.get_backtrace () in
    let exn, info = Exninfo.capture exn in
    let exn_msg = Printexc.to_string exn in
    LIO.trace "fatal error" (exn_msg ^ bt);
    LIO.trace "fatal_error [coq iprint]"
      Pp.(string_of_ppcmds CErrors.(iprint (exn, info)));
    LIO.trace "server crash" (exn_msg ^ bt);
    LIO.logMessage ~lvl:1 ~message:("server crash: " ^ exn_msg)

(* Arguments handling *)
open Cmdliner

let bt =
  let doc = "Enable backtraces" in
  Cmdliner.Arg.(value & flag & info [ "bt" ] ~doc)

let coq_lp_conv ~implicit (unix_path, lp) =
  { Loadpath.coq_path = Libnames.dirpath_of_string lp
  ; unix_path
  ; has_ml = true
  ; implicit
  ; recursive = true
  }

let coqlib =
  let doc =
    "Load Coq.Init.Prelude from $(docv); plugins/ and theories/ should live \
     there."
  in
  Arg.(
    value
    & opt string Coq_config.coqlib
    & info [ "coqlib" ] ~docv:"COQPATH" ~doc)

let rload_path : Loadpath.vo_path list Term.t =
  let doc =
    "Bind a logical loadpath LP to a directory DIR and implicitly open its \
     namespace."
  in
  Term.(
    const List.(map (coq_lp_conv ~implicit:true))
    $ Arg.(
        value
        & opt_all (pair dir string) []
        & info [ "R"; "rec-load-path" ] ~docv:"DIR,LP" ~doc))

let load_path : Loadpath.vo_path list Term.t =
  let doc = "Bind a logical loadpath LP to a directory DIR" in
  Term.(
    const List.(map (coq_lp_conv ~implicit:false))
    $ Arg.(
        value
        & opt_all (pair dir string) []
        & info [ "Q"; "load-path" ] ~docv:"DIR,LP" ~doc))

let ml_include_path : string list Term.t =
  let doc = "Include DIR in default loadpath, for locating ML files" in
  Arg.(
    value & opt_all dir [] & info [ "I"; "ml-include-path" ] ~docv:"DIR" ~doc)

let term_append l =
  Term.(List.(fold_right (fun t l -> const append $ t $ l) l (const [])))

let lsp_cmd : unit Cmd.t =
  let doc = "Coq LSP Server" in
  let man =
    [ `S "DESCRIPTION"
    ; `P "Experimental Coq LSP server"
    ; `S "USAGE"
    ; `P "See the documentation on the project's webpage for more information"
    ]
  in
  let vo_load_path = term_append [ rload_path; load_path ] in
  Cmd.(
    v
      (Cmd.info "coq-lsp" ~version:Version.server ~doc ~man)
      Term.(const lsp_main $ bt $ coqlib $ vo_load_path $ ml_include_path))

let main () =
  let ecode = Cmd.eval lsp_cmd in
  exit ecode

let _ = main ()
