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
(* Copyright 2019-2022 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
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
let _option_empty x =
  match x with
  | None -> true
  | Some _ -> false

let option_cata f d x =
  match x with
  | None -> d
  | Some x -> f x

let option_default x d =
  match x with
  | None -> d
  | Some x -> x

let oint_field name dict = option_cata U.to_int 0 List.(assoc_opt name dict)
let ostring_field name dict = Option.map U.to_string (List.assoc_opt name dict)

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
    ; fb_queue : Coq.Message.t list ref
    }
end

module LIO = Lsp.Io
module LSP = Lsp.Base

(* Request Handling: The client expects a reply *)
module CoqLspOption = struct
  type t = [%import: Fleche.Config.t] [@@deriving yojson]
end

let do_client_options coq_lsp_options =
  LIO.log_info "init" "custom client options:";
  LIO.log_object "init" (`Assoc coq_lsp_options);
  match CoqLspOption.of_yojson (`Assoc coq_lsp_options) with
  | Ok v -> Fleche.Config.v := v
  | Error msg -> LIO.log_error "CoqLspOption.of_yojson error: " msg

let check_client_version version : unit =
  LIO.log_info "version" version;
  match version with
  | "any" | "0.1.2" -> ()
  | v ->
    let message = Format.asprintf "Incorrect version: %s , expected 0.1.2" v in
    LIO.log_error "version" message

let do_initialize ofmt ~id params =
  let trace =
    ostring_field "trace" params
    |> option_cata LIO.TraceValue.parse LIO.TraceValue.Off
  in
  LIO.set_trace_value trace;
  let coq_lsp_options = odict_field "initializationOptions" params in
  do_client_options coq_lsp_options;
  check_client_version !Fleche.Config.v.client_version;
  let client_capabilities = odict_field "capabilities" params in
  LIO.log_info "init" "client capabilities:";
  LIO.log_object "init" (`Assoc client_capabilities);
  let capabilities =
    [ ("textDocumentSync", `Int 1)
    ; ("documentSymbolProvider", `Bool true)
    ; ("hoverProvider", `Bool true)
    ; ("completionProvider", `Assoc [])
    ; ("codeActionProvider", `Bool false)
    ]
  in
  let msg =
    LSP.mk_reply ~id
      ~result:
        (`Assoc
          [ ("capabilities", `Assoc capabilities)
          ; ( "serverInfo"
            , `Assoc
                [ ("name", `String "coq-lsp (C) Inria 2022")
                ; ("version", `String "0.1+alpha")
                ] )
          ])
  in
  LIO.send_json ofmt msg

let do_shutdown ofmt ~id =
  let msg = LSP.mk_reply ~id ~result:`Null in
  LIO.send_json ofmt msg

(* Handler for document *)
module DocHandle = struct
  type t =
    { doc : Fleche.Doc.t
    ; requests : unit (* placeholder for requests attached to a document *)
    }

  let doc_table : (string, t) Hashtbl.t = Hashtbl.create 39

  let create ~uri ~doc =
    (match Hashtbl.find_opt doc_table uri with
    | None -> ()
    | Some _ ->
      LIO.log_error "do_open" ("file " ^ uri ^ " not properly closed by client"));
    Hashtbl.add doc_table uri { doc; requests = () }

  let close ~uri = Hashtbl.remove doc_table uri
  let find ~uri = Hashtbl.find doc_table uri
  let find_doc ~uri = (find ~uri).doc

  let _update ~handle ~(doc : Fleche.Doc.t) =
    Hashtbl.replace doc_table doc.uri { handle with doc }

  (* Clear requests *)
  let update_doc_version ~(doc : Fleche.Doc.t) =
    Hashtbl.replace doc_table doc.uri { doc; requests = () }

  (* trigger pending incremental requests *)
  let update_doc_info ~handle ~(doc : Fleche.Doc.t) =
    Hashtbl.replace doc_table doc.uri { handle with doc }
end

let lsp_of_diags ~uri ~version diags =
  List.map
    (fun { Fleche.Types.Diagnostic.range; severity; message; extra = _ } ->
      (range, severity, message, None))
    diags
  |> LSP.mk_diagnostics ~uri ~version

let lsp_of_progress ~uri ~version progress =
  let progress =
    List.map
      (fun (range, kind) ->
        `Assoc [ ("range", LSP.mk_range range); ("kind", `Int kind) ])
      progress
  in
  let params =
    [ ( "textDocument"
      , `Assoc [ ("uri", `String uri); ("version", `Int version) ] )
    ; ("processing", `List progress)
    ]
  in
  LSP.mk_notification ~method_:"$/coq/fileProgress" ~params

let asts_of_doc doc =
  List.filter_map (fun v -> v.Fleche.Doc.ast) doc.Fleche.Doc.nodes

let diags_of_doc doc =
  List.concat_map (fun node -> node.Fleche.Doc.diags) doc.Fleche.Doc.nodes

module Check = struct
  let pending = ref None

  (* Notification handling; reply is optional / asynchronous *)
  let do_check ofmt ~fb_queue ~uri =
    let handle = DocHandle.find ~uri in
    let doc = Fleche.Doc.check ~ofmt ~doc:handle.doc ~fb_queue in
    DocHandle.update_doc_info ~handle ~doc;
    let diags = diags_of_doc doc in
    let diags = lsp_of_diags ~uri:doc.uri ~version:doc.version diags in
    LIO.send_json ofmt @@ diags

  let completed uri =
    let doc = DocHandle.find_doc ~uri in
    match doc.completed with
    | Yes _ -> true
    | _ -> false

  let schedule ~uri = pending := Some uri
end

let do_open ~state params =
  let document = dict_field "textDocument" params in
  let uri, version, contents =
    ( string_field "uri" document
    , int_field "version" document
    , string_field "text" document )
  in
  let root_state, workspace = State.(state.root_state, state.workspace) in
  let doc =
    Fleche.Doc.create ~state:root_state ~workspace ~uri ~contents ~version
  in
  DocHandle.create ~uri ~doc;
  Check.schedule ~uri

let do_change params =
  let document = dict_field "textDocument" params in
  let uri, version =
    (string_field "uri" document, int_field "version" document)
  in
  let changes = List.map U.to_assoc @@ list_field "contentChanges" params in
  match changes with
  | [] -> ()
  | _ :: _ :: _ ->
    LIO.log_error "do_change"
      "more than one change unsupported due to sync method";
    assert false
  | change :: _ ->
    let contents = string_field "text" change in
    let doc = DocHandle.find_doc ~uri in
    if version > doc.version then (
      LIO.log_info "bump file" (uri ^ " / version: " ^ string_of_int version);
      let tb = Unix.gettimeofday () in
      let doc = Fleche.Doc.bump_version ~version ~contents doc in
      let diff = Unix.gettimeofday () -. tb in
      LIO.log_info "bump file took" (Format.asprintf "%f" diff);
      let () = DocHandle.update_doc_version ~doc in
      Check.schedule ~uri)
    else
      (* That's a weird case, get got changes without a version bump? Do nothing
         for now *)
      ()

let do_close _ofmt params =
  let document = dict_field "textDocument" params in
  let uri = string_field "uri" document in
  DocHandle.close ~uri

let get_textDocument params =
  let document = dict_field "textDocument" params in
  let uri = string_field "uri" document in
  let doc = DocHandle.find_doc ~uri in
  (uri, doc)

let get_position params =
  let pos = dict_field "position" params in
  let line, character = (int_field "line" pos, int_field "character" pos) in
  (line, character)

let mk_syminfo file (name, _path, kind, pos) : J.t =
  `Assoc
    [ ("name", `String name)
    ; ("kind", `Int kind)
    ; (* function *)
      ( "location"
      , `Assoc
          [ ("uri", `String file)
          ; ("range", LSP.mk_range Fleche.Types.(to_range pos))
          ] )
    ]

let _kind_of_type _tm = 13
(* let open Terms in let open Timed in let is_undef = option_empty !(tm.sym_def)
   && List.length !(tm.sym_rules) = 0 in match !(tm.sym_type) with | Vari _ ->
   13 (* Variable *) | Type | Kind | Symb _ | _ when is_undef -> 14 (* Constant
   *) | _ -> 12 (* Function *) *)

let do_symbols ofmt ~id params =
  let uri, doc = get_textDocument params in
  match doc.completed with
  | Yes _ ->
    let f loc id = mk_syminfo uri (Names.Id.to_string id, "", 12, loc) in
    let ast = asts_of_doc doc in
    let slist = Coq.Ast.grab_definitions f ast in
    let msg = LSP.mk_reply ~id ~result:(`List slist) in
    LIO.send_json ofmt msg
  | Stopped _ ->
    (* -32802 = RequestFailed | -32803 = ServerCancelled ; *)
    let code = -32802 in
    let message = "Document is not ready" in
    LSP.mk_request_error ~id ~code ~message |> LIO.send_json ofmt

let do_position_request ofmt ~id params ~handler =
  let _uri, doc = get_textDocument params in
  let point = get_position params in
  let line, col = point in
  let in_range =
    match doc.completed with
    | Yes _ -> true
    | Stopped loc ->
      line < loc.line_nb_last
      || (line = loc.line_nb_last && col <= loc.ep - loc.bol_pos_last)
  in
  if in_range then
    let result = handler ~doc ~point in
    LSP.mk_reply ~id ~result |> LIO.send_json ofmt
  else
    (* -32802 = RequestFailed | -32803 = ServerCancelled ; *)
    let code = -32802 in
    let message = "Document is not ready" in
    LSP.mk_request_error ~id ~code ~message |> LIO.send_json ofmt

let hover_handler ~doc ~point =
  let show_loc_info = true in
  let loc_span = Fleche.Info.LC.loc ~doc ~point Exact in
  let loc_string =
    Option.map Coq.Ast.pr_loc loc_span |> Option.default "no ast"
  in
  let info_string =
    Fleche.Info.LC.info ~doc ~point Exact |> Option.default "no info"
  in
  let hover_string =
    if show_loc_info then loc_string ^ "\n___\n" ^ info_string else info_string
  in
  `Assoc
    ([ ( "contents"
       , `Assoc
           [ ("kind", `String "markdown"); ("value", `String hover_string) ] )
     ]
    @ Option.cata
        (fun loc -> [ ("range", LSP.mk_range (Fleche.Types.to_range loc)) ])
        [] loc_span)

let do_hover ofmt = do_position_request ofmt ~handler:hover_handler

let do_trace params =
  let trace = string_field "value" params in
  LIO.set_trace_value (LIO.TraceValue.parse trace)

(* Replace by ppx when we can print goals properly in the client *)
let mk_hyp { Coq.Goals.names; def = _; ty } : Yojson.Safe.t =
  let names = List.map (fun id -> `String (Names.Id.to_string id)) names in
  let ty = Pp.string_of_ppcmds ty in
  `Assoc [ ("names", `List names); ("ty", `String ty) ]

let mk_goal { Coq.Goals.info = _; ty; hyps } : Yojson.Safe.t =
  let ty = Pp.string_of_ppcmds ty in
  `Assoc [ ("ty", `String ty); ("hyps", `List (List.map mk_hyp hyps)) ]

let mk_goals { Coq.Goals.goals; _ } = List.map mk_goal goals
let mk_goals = Option.cata mk_goals []

let goals_mode =
  if !Fleche.Config.v.goal_after_tactic then Fleche.Info.PrevIfEmpty
  else Fleche.Info.Prev

let goals_handler ~doc ~point =
  let goals = Fleche.Info.LC.goals ~doc ~point goals_mode in
  `Assoc
    [ ( "textDocument"
      , `Assoc [ ("uri", `String doc.uri); ("version", `Int doc.version) ] )
    ; ( "position"
      , `Assoc [ ("line", `Int (fst point)); ("character", `Int (snd point)) ]
      )
    ; ("goals", `List (mk_goals goals))
    ]

let do_goals ofmt = do_position_request ofmt ~handler:goals_handler

let completion_handler ~doc ~point:_ =
  let f _loc id = `Assoc [ ("label", `String Names.Id.(to_string id)) ] in
  let ast = asts_of_doc doc in
  let clist = Coq.Ast.grab_definitions f ast in
  `List clist

let do_completion ofmt = do_position_request ofmt ~handler:completion_handler
let memo_cache_file = ".coq-lsp.cache"

let memo_save_to_disk () =
  try
    Fleche.Memo.save_to_disk ~file:memo_cache_file;
    LIO.log_info "memo" "cache saved to disk"
  with exn ->
    LIO.log_info "memo" (Printexc.to_string exn);
    Sys.remove memo_cache_file;
    ()

(* We disable it for now, see todo.org for more information *)
let memo_save_to_disk () = if false then memo_save_to_disk ()

let memo_read_from_disk () =
  try
    if Sys.file_exists memo_cache_file then (
      LIO.log_info "memo" "trying to load cache file";
      Fleche.Memo.load_from_disk ~file:memo_cache_file;
      LIO.log_info "memo" "cache file loaded")
    else LIO.log_info "memo" "cache file not present"
  with exn ->
    LIO.log_info "memo" ("loading cache failed: " ^ Printexc.to_string exn);
    Sys.remove memo_cache_file;
    ()

let memo_read_from_disk () = if false then memo_read_from_disk ()

(* The rule is: we keep the latest change check notification in the variable; it
   is only served when the rest of requests are served.

   Note that we should add a method to detect stale requests; maybe cancel them
   when a new edit comes.

   Also, this should eventually become a queue, instead of a single
   change_pending setup. *)
let request_queue = Queue.create ()

let process_input (com : J.t) =
  if Fleche.Debug.sched_wakeup then
    LIO.log_info "-> enqueue" (Format.asprintf "%.2f" (Unix.gettimeofday ()));
  (* TODO: this is the place to cancel pending requests that are invalid, and in
     general, to perform queue optimizations *)
  Queue.push com request_queue;
  Control.interrupt := true

exception Lsp_exit

(* XXX: We could split requests and notifications but with the OCaml theading
   model there is not a lot of difference yet; something to think for the
   future. *)
let dispatch_message ofmt ~state dict =
  let id = oint_field "id" dict in
  let params = odict_field "params" dict in
  match string_field "method" dict with
  (* Requests *)
  | "initialize" -> do_initialize ofmt ~id params
  | "shutdown" -> do_shutdown ofmt ~id
  (* Symbols and info about the document *)
  | "textDocument/completion" -> do_completion ofmt ~id params
  | "textDocument/documentSymbol" -> do_symbols ofmt ~id params
  | "textDocument/hover" -> do_hover ofmt ~id params
  (* setTrace *)
  | "$/setTrace" -> do_trace params
  (* Proof-specific stuff *)
  | "proof/goals" -> do_goals ofmt ~id params
  (* Notifications *)
  | "textDocument/didOpen" -> do_open ~state params
  | "textDocument/didChange" -> do_change params
  | "textDocument/didClose" -> do_close ofmt params
  | "textDocument/didSave" -> memo_save_to_disk ()
  | "exit" -> raise Lsp_exit
  (* NOOPs *)
  | "initialized" | "workspace/didChangeWatchedFiles" -> ()
  | msg -> LIO.log_error "no_handler" msg

let dispatch_message ofmt ~state dict =
  try dispatch_message ofmt ~state dict with
  | U.Type_error (msg, obj) -> LIO.log_object msg obj
  | Lsp_exit -> raise Lsp_exit
  | exn ->
    let bt = Printexc.get_backtrace () in
    let iexn = Exninfo.capture exn in
    LIO.log_info "process_queue"
      (if Printexc.backtrace_status () then "bt=true" else "bt=false");
    let method_name = string_field "method" dict in
    LIO.log_info "process_queue" ("exn in method: " ^ method_name);
    LIO.log_info "process_queue" (Printexc.to_string exn);
    LIO.log_info "process_queue" Pp.(string_of_ppcmds CErrors.(iprint iexn));
    LIO.log_info "BT" bt

let rec process_queue ofmt ~state =
  if Fleche.Debug.sched_wakeup then
    LIO.log_info "<- dequeue" (Format.asprintf "%.2f" (Unix.gettimeofday ()));
  (match Queue.peek_opt request_queue with
  | None -> (
    match !Check.pending with
    | Some uri ->
      LIO.log_info "process_queue" "resuming document checking";
      Control.interrupt := false;
      Check.do_check ofmt ~fb_queue:state.State.fb_queue ~uri;
      (* Only if completed! *)
      if Check.completed uri then Check.pending := None
    | None -> Thread.delay 0.1)
  | Some com ->
    (* TODO we should optimize the queue *)
    ignore (Queue.pop request_queue);
    let dict = U.to_assoc com in
    let m = string_field "method" dict in
    LIO.log_info "process_queue" ("Serving Request: " ^ m);
    (* We let Coq work normally now *)
    Control.interrupt := false;
    dispatch_message ofmt ~state dict);
  process_queue ofmt ~state

let lsp_cb oc =
  Fleche.Io.CallBack.
    { log_error = LIO.log_error
    ; send_diagnostics =
        (fun ~uri ~version diags ->
          lsp_of_diags ~uri ~version diags |> Lsp.Io.send_json oc)
    ; send_fileProgress =
        (fun ~uri ~version progress ->
          lsp_of_progress ~uri ~version progress |> Lsp.Io.send_json oc)
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

let mk_fb_handler () =
  let q = ref [] in
  ( (fun Feedback.{ contents; _ } ->
      match contents with
      | Message (((Error | Warning | Notice) as lvl), loc, msg) ->
        add_message lvl loc msg q
      | Message ((Info as lvl), loc, msg) ->
        if !Fleche.Config.v.show_coq_info_messages then
          add_message lvl loc msg q
        else ()
      | Message (Debug, _loc, _msg) -> ()
      | _ -> ())
  , q )

let log_workspace (_, from) =
  let message = "Configuration loaded from " ^ from in
  LIO.log_info "config" message

let lsp_main bt std coqlib vo_load_path ml_include_path =
  LSP.std_protocol := std;
  Exninfo.record_backtrace true;

  let oc = F.std_formatter in

  (* Send a log message *)
  LIO.logMessage oc ~lvl:3 ~message:"Server started";

  Fleche.Io.CallBack.set (lsp_cb oc);

  (* Core Coq initialization *)
  let fb_handler, fb_queue = mk_fb_handler () in
  let debug = bt || Fleche.Debug.backtraces in
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  let root_state =
    Coq.Init.(coq_init { fb_handler; debug; load_module; load_plugin })
  in

  (* Workspace initialization *)
  let options = [] in
  let cmdline =
    { Coq.Workspace.Setup.vo_load_path; ml_include_path; options }
  in
  let workspace = Coq.Workspace.guess ~coqlib ~cmdline in
  log_workspace workspace;

  (* Core LSP loop context *)
  let state = { State.root_state; workspace; fb_queue } in

  memo_read_from_disk ();

  let (_ : Thread.t) = Thread.create (fun () -> process_queue oc ~state) () in

  let rec loop () =
    (* XXX: Implement a queue, compact *)
    let com = LIO.read_request stdin in
    if Fleche.Debug.read then LIO.log_object "read" com;
    process_input com;
    loop ()
  in
  try loop () with
  | (LIO.ReadError "EOF" | Lsp_exit) as exn ->
    let reason =
      "exiting" ^ if exn = Lsp_exit then "" else " [uncontrolled LSP shutdown]"
    in
    LIO.log_error "main" reason
  | exn ->
    let bt = Printexc.get_backtrace () in
    let exn, info = Exninfo.capture exn in
    let exn_msg = Printexc.to_string exn in
    LIO.log_error "fatal error" (exn_msg ^ bt);
    LIO.log_error "fatal_error [coq iprint]"
      Pp.(string_of_ppcmds CErrors.(iprint (exn, info)));
    LIO.log_error "server crash" (exn_msg ^ bt)

(* Arguments handling *)
open Cmdliner

let std =
  let doc = "Restrict to standard LSP protocol" in
  Arg.(value & flag & info [ "std" ] ~doc)

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
      (Cmd.info "coq-lsp" ~version:"0.01" ~doc ~man)
      Term.(const lsp_main $ bt $ std $ coqlib $ vo_load_path $ ml_include_path))

let main () =
  let ecode = Cmd.eval lsp_cmd in
  exit ecode

let _ = main ()
