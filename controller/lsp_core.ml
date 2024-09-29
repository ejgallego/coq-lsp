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

let field name dict =
  try List.(assoc name dict)
  with Not_found ->
    raise (U.Type_error ("field " ^ name ^ " not found", `Assoc dict))

let int_field name dict = U.to_int (field name dict)
let list_field name dict = U.to_list (field name dict)
let string_field name dict = U.to_string (field name dict)
let ofield name dict = List.(assoc_opt name dict)
let ostring_field name dict = Option.map U.to_string (ofield name dict)

module LSP = Lsp.Base
module L = Fleche.Io.Log

module Helpers = struct
  (* XXX helpers; fix to have better errors on wrong protocol code *)
  (* Also note that rely sometimes on "subtyping" of fields, that's something to
     think about better and fix, see #547 *)
  let get_uri params =
    let document =
      match
        field "textDocument" params |> Lsp.Doc.TextDocumentIdentifier.of_yojson
      with
      | Ok uri -> uri
      | Error err ->
        (* ppx_deriving_yojson error messages leave a lot to be desired *)
        (* We use lsp.io here as we will push parsing to the outer loop, so no
           need to reflect this on the type just to undo it later; as this
           message morally doesn't belong here *)
        let message = Format.asprintf "json parsing failed: %s" err in
        Lsp.Io.logMessage ~lvl:Error ~message;
        (* XXX Fixme *)
        CErrors.user_err (Pp.str "failed to parse uri")
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

  let lsp_position_to_tuple (pos : J.t) =
    let pos = U.to_assoc pos in
    let line, character = (int_field "line" pos, int_field "character" pos) in
    (line, character)

  let get_position params =
    let pos = field "position" params in
    lsp_position_to_tuple pos

  let get_position_array params =
    let pos_list = list_field "positions" params in
    List.map lsp_position_to_tuple pos_list
end

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
    ; workspaces : (string * (Coq.Workspace.t, string) Result.t) list
    ; default_workspace : Coq.Workspace.t (* fail safe *)
    }

  open Lsp.Workspace

  let add_workspace ~token state { WorkspaceFolder.uri; _ } =
    let dir = Lang.LUri.File.to_string_file uri in
    let { cmdline; workspaces; _ } = state in
    let ws = Coq.Workspace.guess ~token ~debug:false ~cmdline ~dir in
    { state with workspaces = (dir, ws) :: workspaces }

  let del_workspace state { WorkspaceFolder.uri; _ } =
    let dir = Lang.LUri.File.to_string_file uri in
    { state with workspaces = List.remove_assoc dir state.workspaces }

  let split_in_components path =
    let phase1 = String.split_on_char '/' path in
    let phase2 = List.map (String.split_on_char '\\') phase1 in
    List.concat phase2

  (* This is a bit more tricky in Windows, due to \ vs / paths appearing, so we
     need to first split the dir *)
  let is_in_dir ~dir ~file =
    let dir_c = split_in_components dir in
    let file_c = split_in_components file in
    CList.prefix_of String.equal dir_c file_c

  let workspace_of_uri ~io ~uri ~state =
    let { root_state; workspaces; default_workspace; _ } = state in
    let file = Lang.LUri.File.to_string_file uri in
    match List.find_opt (fun (dir, _) -> is_in_dir ~dir ~file) workspaces with
    | None ->
      Fleche.Io.Report.msg ~io ~lvl:Error "file not in workspace: %s" file;
      (root_state, default_workspace)
    | Some (_, Error _) ->
      Fleche.Io.Report.msg ~io ~lvl:Error "file in errored workspace: %s" file;
      (root_state, default_workspace)
    | Some (_, Ok workspace) -> (root_state, workspace)
end

let do_changeWorkspaceFolders ~ofn:_ ~token ~state params =
  let open Lsp.Workspace in
  let { DidChangeWorkspaceFoldersParams.event } =
    DidChangeWorkspaceFoldersParams.of_yojson (`Assoc params) |> Result.get_ok
  in
  let { WorkspaceFoldersChangeEvent.added; removed } = event in
  let state = List.fold_left (State.add_workspace ~token) state added in
  let state = List.fold_left State.del_workspace state removed in
  state

(* main request module with [answer, postpone, cancel, serve] methods, basically
   IO + glue with the doc_manager *)
module Rq : sig
  module Action : sig
    type t =
      | Immediate of Request.R.t
      | Data of Request.Data.t

    val now : Request.R.t -> t
    val error : int * string -> t
  end

  val serve :
       ofn_rq:(LSP.Response.t -> unit)
    -> token:Coq.Limits.Token.t
    -> id:int
    -> Action.t
    -> unit

  val cancel :
    ofn_rq:(LSP.Response.t -> unit) -> code:int -> message:string -> int -> unit

  val serve_postponed :
       ofn_rq:(LSP.Response.t -> unit)
    -> token:Coq.Limits.Token.t
    -> doc:Fleche.Doc.t
    -> Int.Set.t
    -> unit
end = struct
  (* Answer a request, private *)
  let answer ~ofn_rq ~id result =
    (match result with
    | Result.Ok result -> LSP.Response.mk_ok ~id ~result
    | Error (code, message) -> LSP.Response.mk_error ~id ~code ~message)
    |> ofn_rq

  (* private to the Rq module, just used not to retrigger canceled requests *)
  let _rtable : (int, Request.Data.t) Hashtbl.t = Hashtbl.create 673

  let postpone_ ~id (pr : Request.Data.t) =
    if Fleche.Debug.request_delay then L.trace "request" "postponing rq: %d" id;
    Hashtbl.add _rtable id pr

  (* Consumes a request, if alive, it answers mandatorily *)
  let consume_ ~ofn_rq ~f id =
    match Hashtbl.find_opt _rtable id with
    | Some pr ->
      Hashtbl.remove _rtable id;
      f pr |> answer ~ofn_rq ~id
    | None ->
      L.trace "consuem" "can't consume cancelled request: %d" id;
      ()

  let cancel ~ofn_rq ~code ~message id : unit =
    (* fail the request, do cleanup first *)
    let f pr =
      let () =
        let uri, postpone, request = Request.Data.dm_request pr in
        Fleche.Theory.Request.remove { id; uri; postpone; request }
      in
      Error (code, message)
    in
    consume_ ~ofn_rq ~f id

  let debug_serve id pr =
    if Fleche.Debug.request_delay then
      L.trace "serving" "rq: %d | %a" id Request.Data.data pr

  let serve_postponed ~ofn_rq ~token ~doc id =
    let f pr =
      debug_serve id pr;
      Request.Data.serve ~token ~doc pr
    in
    consume_ ~ofn_rq ~f id

  let query ~ofn_rq ~token ~id (pr : Request.Data.t) =
    let uri, postpone, request = Request.Data.dm_request pr in
    match Fleche.Theory.Request.add { id; uri; postpone; request } with
    | Cancel ->
      let code = -32802 in
      let message = "Document is not ready" in
      Error (code, message) |> answer ~ofn_rq ~id
    | Now doc ->
      debug_serve id pr;
      Request.Data.serve ~token ~doc pr |> answer ~ofn_rq ~id
    | Postpone -> postpone_ ~id pr

  module Action = struct
    type t =
      | Immediate of Request.R.t
      | Data of Request.Data.t

    let now r = Immediate r
    let error (code, msg) = now (Error (code, msg))
  end

  let serve ~ofn_rq ~token ~id action =
    match action with
    | Action.Immediate r -> answer ~ofn_rq ~id r
    | Action.Data p -> query ~ofn_rq ~token ~id p

  let serve_postponed ~ofn_rq ~token ~doc rl =
    Int.Set.iter (serve_postponed ~ofn_rq ~token ~doc) rl
end

(***********************************************************************)
(* Start of protocol handlers: document notifications                  *)

let do_open ~io ~token ~(state : State.t) params =
  let document =
    field "textDocument" params
    |> Lsp.Doc.TextDocumentItem.of_yojson |> Result.get_ok
  in
  let Lsp.Doc.TextDocumentItem.{ uri; version; text; _ } = document in
  let init, workspace = State.workspace_of_uri ~io ~uri ~state in
  let files = Coq.Files.make () in
  let env = Fleche.Doc.Env.make ~init ~workspace ~files in
  Fleche.Theory.create ~io ~token ~env ~uri ~raw:text ~version

let do_change ~ofn_rq ~io ~token params =
  let uri, version = Helpers.get_uri_version params in
  let changes = List.map U.to_assoc @@ list_field "contentChanges" params in
  match changes with
  | [] ->
    L.trace "do_change" "no change in changes? ignoring";
    ()
  | _ :: _ :: _ ->
    L.trace "do_change"
      "more than one change unsupported due to sync method, ignoring";
    ()
  | change :: _ ->
    let raw = string_field "text" change in
    let invalid_rq = Fleche.Theory.change ~io ~token ~uri ~version ~raw in
    let code = -32802 in
    let message = "Request got old in server" in
    Int.Set.iter (Rq.cancel ~ofn_rq ~code ~message) invalid_rq

let do_close params =
  let uri = Helpers.get_uri params in
  Fleche.Theory.close ~uri

let do_trace params =
  let trace = string_field "value" params in
  match Lsp.Io.TraceValue.of_string trace with
  | Ok t -> Lsp.Io.set_trace_value t
  | Error e -> L.trace "$/setTrace" "invalid value: %s" e

(***********************************************************************)
(* Start of protocol handlers: document requests                       *)

let do_shutdown = Rq.Action.now (Ok `Null)

let do_position_request ~postpone ~params ~handler =
  let uri, version = Helpers.get_uri_oversion params in
  let point = Helpers.get_position params in
  Rq.Action.Data
    (Request.Data.PosRequest { uri; handler; point; version; postpone })

(* XXX Duplicate with theory.ml; inverse comparsion so larger points come
   first *)
let compare p1 p2 =
  let x1, y1 = p1 in
  let x2, y2 = p2 in
  let xres = Int.compare x1 x2 in
  if xres = 0 then -Int.compare y1 y2 else -xres

(* A little bit hacky, but selectionRange is the only request that needs this...
   so we will survive *)
let do_position_list_request ~postpone ~params ~handler =
  let uri, version = Helpers.get_uri_oversion params in
  let points = Helpers.get_position_array params in
  match points with
  | [] ->
    let point, handler = ((0, 0), Request.empty) in
    Rq.Action.Data
      (Request.Data.PosRequest { uri; handler; point; version; postpone })
  | points ->
    let handler = handler ~points in
    let point = List.hd (List.sort compare points) in
    Rq.Action.Data
      (Request.Data.PosRequest { uri; handler; point; version; postpone })

let do_hover = do_position_request ~postpone:false ~handler:Rq_hover.hover

let do_selectionRange =
  do_position_list_request ~postpone:false ~handler:Rq_selectionRange.request

(* We get the format from the params *)
let get_pp_format_from_config () =
  match !Fleche.Config.v.pp_type with
  | 0 -> Rq_goals.Str
  | 1 -> Rq_goals.Pp
  | v ->
    L.trace "get_pp_format_from_config" "unknown output parameter: %d" v;
    Rq_goals.Str

let get_pp_format params =
  match ostring_field "pp_format" params with
  | Some "Pp" -> Rq_goals.Pp
  | Some "Str" -> Rq_goals.Str
  | Some v ->
    L.trace "get_pp_format" "error in parameter: %s" v;
    get_pp_format_from_config ()
  | None -> get_pp_format_from_config ()

let get_pretac params =
  Option.append (ostring_field "command" params) (ostring_field "pretac" params)

let get_goals_mode_from_config () =
  if !Fleche.Config.v.goal_after_tactic then Fleche.Info.PrevIfEmpty
  else Fleche.Info.Prev

let get_goals_mode params =
  match ostring_field "mode" params with
  | Some "Prev" -> Fleche.Info.Prev
  | Some "After" -> Fleche.Info.PrevIfEmpty
  | Some v ->
    L.trace "get_goals_mode" "error in parameter: %s" v;
    get_goals_mode_from_config ()
  | None -> get_goals_mode_from_config ()

let do_goals ~params =
  let pp_format = get_pp_format params in
  let mode = get_goals_mode params in
  let pretac = get_pretac params in
  let handler = Rq_goals.goals ~pp_format ~mode ~pretac () in
  do_position_request ~postpone:true ~handler ~params

let do_definition =
  do_position_request ~postpone:true ~handler:Rq_definition.request

let do_completion =
  do_position_request ~postpone:true ~handler:Rq_completion.completion

(* Requires the full document to be processed *)
let do_document_request ~postpone ~params ~handler =
  let uri = Helpers.get_uri params in
  Rq.Action.Data (Request.Data.DocRequest { uri; postpone; handler })

(* Don't postpone when in lazy mode *)
let do_document_request_maybe ~params ~handler =
  let postpone = not !Fleche.Config.v.check_only_on_request in
  do_document_request ~postpone ~params ~handler

let do_immediate ~params ~handler =
  let uri = Helpers.get_uri params in
  Rq.Action.Data (Request.Data.Immediate { uri; handler })

(* new immediate mode, cc: #816 *)
let do_symbols ~params =
  let handler = Rq_symbols.symbols in
  if !Fleche.Config.v.check_only_on_request then do_immediate ~params ~handler
  else do_document_request ~postpone:true ~params ~handler

let do_document = do_document_request_maybe ~handler:Rq_document.request
let do_save_vo = do_document_request_maybe ~handler:Rq_save.request
let do_lens = do_document_request_maybe ~handler:Rq_lens.request

(* could be smarter *)
let do_action ~params =
  let range = field "range" params in
  match Lsp.JLang.Diagnostic.Range.of_yojson range with
  | Ok range ->
    let range = Lsp.JLang.Diagnostic.Range.vnoc range in
    do_immediate ~params ~handler:(Rq_action.request ~range)
  | Error err ->
    (* XXX: We really need to fix the parsing error handling in lsp_core, we got
       it right in petanque haha *)
    (* JSON-RPC Parse error (EJGA: is this the right code) *)
    let code = -32700 in
    Rq.Action.error (code, err)

let do_cancel ~ofn_rq ~params =
  let id = int_field "id" params in
  let code = -32800 in
  let message = "Cancelled by client" in
  Rq.cancel ~ofn_rq ~code ~message id

let do_cache_trim ~io = Nt_cache_trim.notification ~io

let do_viewRange params =
  match List.assoc "range" params |> Lsp.JLang.Diagnostic.Range.of_yojson with
  | Ok range ->
    let { Lsp.JLang.Diagnostic.Range.end_ = { line; character }; _ } = range in
    L.trace "viewRange" "l: %d c:%d" line character;
    let uri = Helpers.get_uri params in
    Fleche.Theory.Check.set_scheduler_hint ~uri ~point:(line, character);
    ()
  | Error err -> L.trace "viewRange" "error in parsing notification: %s" err

let do_changeConfiguration ~io params =
  Fleche.Io.Report.msg ~io ~lvl:Info "didChangeReceived";
  let settings = field "settings" params |> U.to_assoc in
  Rq_init.do_settings settings;
  ()

(* EJGA: Note that our current configuration allow petanque calls to be
   interrupted, this can become an issue with LSP. For now, clients must choose
   a trade-off (we could disable interruption on petanque call, but that brings
   other downsides)

   The only real solution is to wait for OCaml 5.x support, so we can server
   read-only queries without interrupting the main Coq thread. *)
let petanque_handle ~token =
  let open Petanque_json in
  function
  | Interp.Action.Now handler -> Rq.Action.now (handler ~token)
  | Interp.Action.Doc { uri; handler } ->
    (* Request document execution if not ready *)
    let postpone = true in
    Rq.Action.(Data (DocRequest { uri; postpone; handler }))

let do_petanque ~token method_ params =
  let open Petanque_json in
  let do_handle = petanque_handle in
  let unhandled ~token:_ ~method_ =
    (* JSON-RPC method not found *)
    let code = -32601 in
    let message = Format.asprintf "method %s not found" method_ in
    Rq.Action.error (code, message)
  in
  Interp.handle_request ~do_handle ~unhandled ~token ~method_ ~params

(***********************************************************************)

(** LSP Init routine *)
exception Lsp_exit

let log_workspace ~io (dir, w) =
  let message, extra = Coq.Workspace.describe_guess w in
  L.trace "workspace" ~extra "initialized %s" dir;
  Fleche.Io.Report.msg ~io ~lvl:Info "%s" message

let version () =
  let dev_version =
    match Build_info.V1.version () with
    | None -> "N/A"
    | Some bi -> Build_info.V1.Version.to_string bi
  in
  Format.asprintf "version %s, dev: %s, Coq version: %s, OS: %s"
    Fleche.Version.server dev_version Coq_config.version Sys.os_type

module Init_effect = struct
  type t =
    | Success of (string * (Coq.Workspace.t, string) Result.t) list
    | Loop
    | Exit
end

let serverInfo =
  let coq = Coq_config.version in
  let ocaml = Sys.ocaml_version in
  let coq_lsp = Fleche.Version.server in
  Fleche.ServerInfo.Version.{ coq; ocaml; coq_lsp }

let lsp_init_process ~ofn ~io ~cmdline ~debug msg : Init_effect.t =
  let ofn_rq r = Lsp.Base.Message.response r |> ofn in
  let ofn_nt r = Lsp.Base.Message.notification r |> ofn in
  match msg with
  | LSP.Message.Request { method_ = "initialize"; id; params } ->
    (* At this point logging is allowed per LSP spec *)
    Fleche.Io.Report.msg ~io ~lvl:Info "Initializing coq-lsp server %s"
      (version ());
    let token = Coq.Limits.Token.create () in
    let result, dirs = Rq_init.do_initialize ~io ~params in
    Rq.Action.now (Ok result) |> Rq.serve ~ofn_rq ~token ~id;
    Lsp.JFleche.mk_serverVersion serverInfo |> ofn_nt;
    Fleche.Io.Report.msg ~io ~lvl:Info "Server initializing (int_backend: %s)"
      (Coq.Limits.name ());
    (* Workspace initialization *)
    let debug = debug || !Fleche.Config.v.debug in
    let workspaces =
      List.map
        (fun dir -> (dir, Coq.Workspace.guess ~token ~cmdline ~debug ~dir))
        dirs
    in
    List.iter (log_workspace ~io) workspaces;
    Success workspaces
  | LSP.Message.Request { id; _ } ->
    (* per spec *)
    LSP.Response.mk_error ~id ~code:(-32002) ~message:"server not initialized"
    |> ofn_rq;
    Loop
  | LSP.Message.Notification { method_ = "exit"; params = _ } -> Exit
  | LSP.Message.Notification _ ->
    (* We can't log before getting the initialize message *)
    Loop
  | LSP.Message.Response _ ->
    (* O_O *)
    Loop

(** Dispatching *)
let dispatch_notification ~io ~ofn ~token ~state ~method_ ~params : unit =
  let ofn_rq r = Lsp.Base.Message.response r |> ofn in
  match method_ with
  (* Lifecycle *)
  | "exit" -> raise Lsp_exit
  (* setTrace and settings *)
  | "$/setTrace" -> do_trace params
  | "workspace/didChangeConfiguration" -> do_changeConfiguration ~io params
  (* Document lifetime *)
  | "textDocument/didOpen" -> do_open ~io ~token ~state params
  | "textDocument/didChange" -> do_change ~io ~ofn_rq ~token params
  | "textDocument/didClose" -> do_close params
  | "textDocument/didSave" -> Cache.save_to_disk ()
  (* Specific to coq-lsp *)
  | "coq/viewRange" -> do_viewRange params
  | "coq/trimCaches" -> do_cache_trim ~io
  (* Cancel Request *)
  | "$/cancelRequest" -> do_cancel ~ofn_rq ~params
  (* NOOPs *)
  | "initialized" -> ()
  (* Generic handler *)
  | msg -> L.trace "no_handler" "%s" msg

let dispatch_state_notification ~io ~ofn ~token ~state ~method_ ~params :
    State.t =
  match method_ with
  (* Workspace *)
  | "workspace/didChangeWorkspaceFolders" ->
    do_changeWorkspaceFolders ~ofn ~token ~state params
  | _ ->
    dispatch_notification ~io ~ofn ~token ~state ~method_ ~params;
    state

let dispatch_request ~token ~method_ ~params : Rq.Action.t =
  match method_ with
  (* Lifecyle *)
  | "initialize" ->
    L.trace "dispatch_request" "duplicate initialize request! Rejecting";
    (* XXX what's the error code here *)
    Rq.Action.error (-32600, "Invalid Request: server already initialized")
  | "shutdown" -> do_shutdown
  (* Symbols and info about the document *)
  | "textDocument/completion" -> do_completion ~params
  | "textDocument/definition" -> do_definition ~params
  | "textDocument/documentSymbol" -> do_symbols ~params
  | "textDocument/hover" -> do_hover ~params
  | "textDocument/codeLens" -> do_lens ~params
  | "textDocument/selectionRange" -> do_selectionRange ~params
  | "textDocument/codeAction" -> do_action ~params
  (* Proof-specific stuff *)
  | "proof/goals" -> do_goals ~params
  (* Proof-specific stuff *)
  | "coq/saveVo" -> do_save_vo ~params
  (* Coq specific stuff *)
  | "coq/getDocument" -> do_document ~params
  (* Petanque embedding *)
  | msg when Coq.Compat.Ocaml_413.String.starts_with ~prefix:"petanque/" msg ->
    do_petanque msg ~token params
  (* Generic handler *)
  | msg ->
    L.trace "no_handler" "%s" msg;
    Rq.Action.error (-32601, "method not found")

let dispatch_request ~ofn_rq ~token ~id ~method_ ~params =
  dispatch_request ~token ~method_ ~params |> Rq.serve ~ofn_rq ~token ~id

let dispatch_message ~io ~ofn ~token ~state (com : LSP.Message.t) : State.t =
  let ofn_rq r = Lsp.Base.Message.response r |> ofn in
  match com with
  | Notification { method_; params } ->
    L.trace "process_queue" "Serving notification: %s" method_;
    dispatch_state_notification ~io ~ofn ~token ~state ~method_ ~params
  | Request { id; method_; params } ->
    L.trace "process_queue" "Serving Request: %s" method_;
    dispatch_request ~ofn_rq ~token ~id ~method_ ~params;
    state
  | Response r ->
    L.trace "process_queue" "Serving response for: %d" (Lsp.Base.Response.id r);
    state

(* Queue handling *)

(***********************************************************************)
(* The queue strategy is: we keep pending document checks in Fleche.Theory, they
   are only resumed when the rest of requests in the queue are served.

   Note that we should add a method to detect stale requests; maybe cancel them
   when a new edit comes. *)

let current_token = ref None

let token_factory () =
  let token = Coq.Limits.Token.create () in
  current_token := Some token;
  token

let set_current_token () =
  match !current_token with
  | None -> ()
  | Some tok ->
    current_token := None;
    Coq.Limits.Token.set tok

type 'a cont =
  | Cont of 'a
  | Yield of 'a

let check_or_yield ~io ~ofn ~token ~state =
  let ofn_rq r = Lsp.Base.Message.response r |> ofn in
  match Fleche.Theory.Check.maybe_check ~io ~token with
  | None -> Yield state
  | Some (ready, doc) ->
    let () = Rq.serve_postponed ~ofn_rq ~token ~doc ready in
    Cont state

module LspQueue : sig
  val pop_opt : unit -> LSP.Message.t option
  val push_and_optimize : LSP.Message.t -> unit
end = struct
  let request_queue = Queue.create ()

  let pop_opt () =
    match Queue.peek_opt request_queue with
    | None -> None
    | Some v ->
      ignore (Queue.pop request_queue);
      Some v

  let analyze = function
    | LSP.Message.Notification { method_ = "textDocument/didChange"; params } ->
      let uri, version = Helpers.get_uri_version params in
      Some (uri, version)
    | _ -> None

  let filter_queue _d = ()

  (* TODO: optimize the queue? EJGA: I've found that VS Code as a client keeps
     the queue tidy by itself, so this works fine as now *)
  let push_and_optimize com =
    let filter_data = analyze com in
    filter_queue filter_data;
    Queue.push com request_queue
end

let dispatch_or_resume_check ~io ~ofn ~state =
  match LspQueue.pop_opt () with
  | None ->
    (* This is where we make progress on document checking; kind of IDLE
       workqueue. *)
    let token = token_factory () in
    check_or_yield ~io ~ofn ~token ~state
  | Some com ->
    (* We let Coq work normally now *)
    let token = token_factory () in
    Cont (dispatch_message ~io ~ofn ~token ~state com)

(* Wrapper for the top-level call *)
let dispatch_or_resume_check ~io ~ofn ~state =
  try Some (dispatch_or_resume_check ~io ~ofn ~state) with
  | U.Type_error (msg, obj) ->
    L.trace_object msg obj;
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
    L.trace "process_queue" "%s"
      (if Printexc.backtrace_status () then "bt=true" else "bt=false");
    (* let method_name = LSP.Message.method_ com in *)
    (* L.trace "process_queue" "exn in method: %s" method_name; *)
    L.trace "print_exn [OCaml]" "%s" (Printexc.to_string exn);
    L.trace "print_exn [Coq  ]" "%a" Pp.pp_with CErrors.(iprint iexn);
    L.trace "print_bt  [OCaml]" "%s" bt;
    Some (Yield state)

let enqueue_message (com : LSP.Message.t) =
  if Fleche.Debug.sched_wakeup then
    L.trace "-> enqueue" "%.2f" (Unix.gettimeofday ());
  (* TODO: this is the place to cancel pending requests that are invalid, and in
     general, to perform queue optimizations *)
  LspQueue.push_and_optimize com;
  set_current_token ()

module CB (O : sig
  val ofn : Lsp.Base.Notification.t -> unit
end) =
struct
  let ofn = O.ofn
  let trace _hdr ?extra message = Lsp.Io.logTrace ~message ~extra
  let message ~lvl ~message = Lsp.Io.logMessage ~lvl ~message

  let diagnostics ~uri ~version diags =
    Lsp.Core.mk_diagnostics ~uri ~version diags |> ofn

  let fileProgress ~uri ~version progress =
    Lsp.JFleche.mk_progress ~uri ~version progress |> ofn

  let perfData ~uri ~version perf =
    Lsp.JFleche.mk_perf ~uri ~version perf |> ofn

  let serverVersion vi = Lsp.JFleche.mk_serverVersion vi |> ofn
  let serverStatus st = Lsp.JFleche.mk_serverStatus st |> ofn

  let cb =
    Fleche.Io.CallBack.
      { trace
      ; message
      ; diagnostics
      ; fileProgress
      ; perfData
      ; serverVersion
      ; serverStatus
      }
end
