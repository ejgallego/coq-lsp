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
module L = Fleche.Io.Log
open Controller
open Lsp_core

(* Do cleanup here if necessary *)
let exit_message ~io = Fleche.Io.Report.msg ~io ~lvl:Error "server exiting"
let lsp_cleanup ~io = exit_message ~io

let rec process_queue ~delay ~io ~ofn ~state : unit =
  if Fleche.Debug.sched_wakeup then
    L.trace "<- dequeue" "%.2f" (Unix.gettimeofday ());
  match dispatch_or_resume_check ~io ~ofn ~state with
  | None ->
    (* As of now, we exit the whole program here, we could try an experiment to
       invert the threads, so the I/O routine is a thread and process_queue is
       the main driver *)
    lsp_cleanup ~io;
    (* We can't use [Thread.exit] here as the main thread will be blocked on
       I/O *)
    exit 0
  | Some (Yield state) ->
    Thread.delay delay;
    process_queue ~delay ~io ~ofn ~state
  | Some (Cont state) -> process_queue ~delay ~io ~ofn ~state

let concise_cb ofn =
  let diagnostics ~uri ~version diags =
    if List.length diags > 0 then
      Lsp.Core.mk_diagnostics ~uri ~version diags |> ofn
  in
  Fleche.Io.CallBack.
    { trace = (fun _hdr ?extra:_ _msg -> ())
    ; message = (fun ~lvl:_ ~message:_ -> ())
    ; diagnostics
    ; fileProgress = (fun ~uri:_ ~version:_ _progress -> ())
    ; perfData = (fun ~uri:_ ~version:_ _perf -> ())
    ; serverVersion = (fun _ -> ())
    ; serverStatus = (fun _ -> ())
    }

(* Main loop *)
let coq_init ~debug =
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  let vm, warnings = (true, None) in
  Coq.Init.(coq_init { debug; load_module; load_plugin; vm; warnings })

let exit_notification =
  Lsp.Base.Message.(Notification { method_ = "exit"; params = [] })

let rec lsp_init_loop ~io ~ifn ~ofn ~cmdline ~debug =
  match ifn () with
  | None -> raise Lsp_exit
  | Some (Ok msg) -> (
    match lsp_init_process ~io ~ofn ~cmdline ~debug msg with
    | Init_effect.Exit -> raise Lsp_exit
    | Init_effect.Loop -> lsp_init_loop ~io ~ifn ~ofn ~cmdline ~debug
    | Init_effect.Success w -> w)
  | Some (Error err) ->
    L.trace "read_request" "error: %s" err;
    lsp_init_loop ~io ~ifn ~ofn ~cmdline ~debug

let lsp_main bt coqcorelib coqlib findlib_config ocamlpath vo_load_path
    ml_include_path require_libraries delay int_backend =
  Coq.Limits.select_best int_backend;
  Coq.Limits.start ();

  (* Try to be sane w.r.t. \r\n in Windows *)
  Stdlib.set_binary_mode_in stdin true;
  Stdlib.set_binary_mode_out stdout true;

  (* We output to stdout *)
  let ifn () = Lsp.Io.read_message stdin in

  (* Set log channels *)
  let ofn message = Lsp.Io.send_message Format.std_formatter message in
  let ofn_ntn not = Lsp.Base.Message.notification not |> ofn in

  Lsp.Io.set_log_fn ofn_ntn;

  let module CB = Lsp_core.CB (struct
    let ofn = ofn_ntn
  end) in
  let io = CB.cb in
  Fleche.Io.CallBack.set io;

  (* IMPORTANT: LSP spec forbids any message from server to client before
     initialize is received *)

  (* Core Coq initialization *)
  let debug = bt || Fleche.Debug.backtraces in
  let root_state = coq_init ~debug in
  let cmdline =
    { Coq.Workspace.CmdLine.coqcorelib
    ; coqlib
    ; findlib_config
    ; ocamlpath
    ; vo_load_path
    ; ml_include_path
    ; args = []
    ; require_libraries
    }
  in

  (* Read JSON-RPC messages and push them to the queue *)
  let rec read_loop () =
    match ifn () with
    | None ->
      (* EOF, push an exit notication to the queue *)
      enqueue_message exit_notification
    | Some (Ok msg) ->
      enqueue_message msg;
      read_loop ()
    | Some (Error err) ->
      L.trace "read_request" "error: %s" err;
      read_loop ()
  in

  (* Input/output will happen now *)
  try
    (* LSP Server server initialization *)
    let workspaces = lsp_init_loop ~io ~ifn ~ofn ~cmdline ~debug in
    let io =
      if !Fleche.Config.v.verbosity < 2 then (
        Fleche.Config.(
          v := { !v with send_diags = false; send_perf_data = false });
        Lsp.Io.set_log_fn (fun _obj -> ());
        let io = concise_cb ofn_ntn in
        Fleche.Io.CallBack.set io;
        io)
      else io
    in

    (* Core LSP loop context *)
    let default_workspace = Coq.Workspace.default ~debug ~cmdline in
    let state = { State.root_state; cmdline; workspaces; default_workspace } in

    (* Read workspace state (noop for now) *)
    Cache.read_from_disk ();

    let pfn () : unit = process_queue ~delay ~io ~ofn ~state in
    let (_ : Thread.t) = Thread.create pfn () in

    read_loop ()
  with
  | Lsp_exit -> Fleche.Io.Report.msg ~io ~lvl:Error "[LSP shutdown] EOF\n"
  | exn ->
    let bt = Printexc.get_backtrace () in
    let exn, info = Exninfo.capture exn in
    let exn_msg = Printexc.to_string exn in
    L.trace "fatal error" "%s\n%s" exn_msg bt;
    L.trace "fatal_error [coq iprint]" "%a" Pp.pp_with
      CErrors.(iprint (exn, info));
    L.trace "server crash" "%s\n%s" exn_msg bt;
    Fleche.Io.Report.msg ~io ~lvl:Error
      "[uncontrolled LSP shutdown] server crash:\n%s" exn_msg

(* Arguments handling *)
open Cmdliner

let delay : float Term.t =
  let doc = "Delay value in seconds when server is idle" in
  Arg.(value & opt float 0.1 & info [ "D"; "idle-delay" ] ~docv:"DELAY" ~doc)

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
  let open Coq.Args in
  let vo_load_path = term_append [ rload_paths; qload_paths ] in
  Cmd.(
    v
      (Cmd.info "coq-lsp" ~version:Fleche.Version.server ~doc ~man)
      Term.(
        const lsp_main $ bt $ coqcorelib $ coqlib $ findlib_config $ ocamlpath
        $ vo_load_path $ ml_include_path $ ri_from $ delay $ int_backend))

let main () =
  let ecode = Cmd.eval lsp_cmd in
  exit ecode

let () = main ()
