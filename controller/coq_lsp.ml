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

(* This is the native-specific Code for the implementation of the event queue
   based in OCaml threads. *)

module U = Yojson.Safe.Util
module LIO = Lsp.Io
module LSP = Lsp.Base
open Controller
open Lsp_core

(***********************************************************************)
(* The queue strategy is: we keep pending document checks in Doc_manager, they
   are only resumed when the rest of requests in the queue are served.

   Note that we should add a method to detect stale requests; maybe cancel them
   when a new edit comes. *)

(** Main event queue *)
let request_queue = Queue.create ()

let check_or_yield ~ofmt =
  match Doc_manager.Check.maybe_check ~ofmt with
  | None -> Thread.delay 0.1
  | Some ready -> serve_postponed_requests ~ofmt ready

let dispatch_or_resume_check ~ofmt ~state =
  match Queue.peek_opt request_queue with
  | None ->
    (* This is where we make progress on document checking; kind of IDLE
       workqueue. *)
    Control.interrupt := false;
    check_or_yield ~ofmt;
    state
  | Some com ->
    (* TODO: optimize the queue? EJGA: I've found that VS Code as a client keeps
       the queue tidy by itself, so this works fine as now *)
    ignore (Queue.pop request_queue);
    LIO.trace "process_queue" ("Serving Request: " ^ LSP.Message.method_ com);
    (* We let Coq work normally now *)
    Control.interrupt := false;
    dispatch_message ~ofmt ~state com

(* Wrapper for the top-level call *)
let dispatch_or_resume_check ~ofmt ~state =
  try Some (dispatch_or_resume_check ~ofmt ~state) with
  | U.Type_error (msg, obj) ->
    LIO.trace_object msg obj;
    Some state
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
    Some state

(* Do cleanup here if necessary *)
let exit_message () =
  let message = "server exiting" in
  LIO.logMessage ~lvl:1 ~message

let lsp_cleanup () = exit_message ()

let rec process_queue ofmt ~state =
  if Fleche.Debug.sched_wakeup then
    LIO.trace "<- dequeue" (Format.asprintf "%.2f" (Unix.gettimeofday ()));
  match dispatch_or_resume_check ~ofmt ~state with
  | None ->
    (* As of now, we exit the whole program here, we could try an experiment to
       invert the threads, so the I/O routine is a thread and process_queue is
       the main driver *)
    lsp_cleanup ();
    (* We can't use [Thread.exit] here as the main thread will be blocked on
       I/O *)
    exit 0
  | Some state -> process_queue ofmt ~state

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
          Lsp.JLang.mk_diagnostics ~uri ~version diags |> Lsp.Io.send_json ofmt)
    ; send_fileProgress =
        (fun ~ofmt ~uri ~version progress ->
          Lsp.JFleche.mk_progress ~uri ~version progress
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
  | Message (lvl, loc, msg) -> add_message lvl loc msg q
  | _ -> ()

let coq_init ~fb_queue ~debug =
  let fb_handler = mk_fb_handler fb_queue in
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  Coq.Init.(coq_init { fb_handler; debug; load_module; load_plugin })

let exit_notification =
  Lsp.Base.Message.(Notification { method_ = "exit"; params = [] })

let lsp_main bt coqlib vo_load_path ml_include_path =
  (* We output to stdout *)
  let ic = stdin in
  let oc = Format.std_formatter in

  (* Set log channels *)
  LIO.set_log_channel oc;
  Fleche.Io.CallBack.set lsp_cb;

  (* IMPORTANT: LSP spec forbids any message from server to client before
     initialize is received *)

  (* Core Coq initialization *)
  let fb_queue = Coq.Protect.fb_queue in

  let debug = bt || Fleche.Debug.backtraces in
  let root_state = coq_init ~fb_queue ~debug in
  let cmdline =
    { Coq.Workspace.CmdLine.coqlib; vo_load_path; ml_include_path }
  in

  (* Read JSON-RPC messages and push them to the queue *)
  let rec read_loop () =
    match LIO.read_request ic with
    | None ->
      (* EOF, push an exit notication to the queue *)
      process_input exit_notification
    | Some msg ->
      process_input msg;
      read_loop ()
  in

  (* Input/output will happen now *)
  try
    (* LSP Server server initialization *)
    let workspaces = lsp_init_loop ic oc ~cmdline ~debug in

    (* Core LSP loop context *)
    let state = { State.root_state; cmdline; workspaces } in

    (* Read workspace state (noop for now) *)
    Cache.read_from_disk ();

    let (_ : Thread.t) = Thread.create (fun () -> process_queue oc ~state) () in

    read_loop ()
  with exn ->
    let bt = Printexc.get_backtrace () in
    let exn, info = Exninfo.capture exn in
    let exn_msg = Printexc.to_string exn in
    LIO.trace "fatal error" (exn_msg ^ bt);
    LIO.trace "fatal_error [coq iprint]"
      Pp.(string_of_ppcmds CErrors.(iprint (exn, info)));
    LIO.trace "server crash" (exn_msg ^ bt);
    let message = "[uncontrolled LSP shutdown] server crash\n" ^ exn_msg in
    LIO.logMessage ~lvl:1 ~message

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
    ; `P "Coq LSP server"
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

let () = main ()
