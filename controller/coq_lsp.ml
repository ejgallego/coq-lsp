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

(* Do cleanup here if necessary *)
let exit_message () =
  let message = "server exiting" in
  LIO.logMessage ~lvl:1 ~message

let lsp_cleanup () = exit_message ()

let rec process_queue ~ofn ~state =
  if Fleche.Debug.sched_wakeup then
    LIO.trace "<- dequeue" (Format.asprintf "%.2f" (Unix.gettimeofday ()));
  match dispatch_or_resume_check ~ofn ~state with
  | None ->
    (* As of now, we exit the whole program here, we could try an experiment to
       invert the threads, so the I/O routine is a thread and process_queue is
       the main driver *)
    lsp_cleanup ();
    (* We can't use [Thread.exit] here as the main thread will be blocked on
       I/O *)
    exit 0
  | Some (Yield state) ->
    Thread.delay 0.01;
    process_queue ~ofn ~state
  | Some (Cont state) -> process_queue ~ofn ~state

(* Main loop *)
let lsp_cb =
  Fleche.Io.CallBack.
    { trace = LIO.trace
    ; send_diagnostics =
        (fun ~ofn ~uri ~version diags ->
          Lsp.JLang.mk_diagnostics ~uri ~version diags |> ofn)
    ; send_fileProgress =
        (fun ~ofn ~uri ~version progress ->
          Lsp.JFleche.mk_progress ~uri ~version progress |> ofn)
    }

let coq_init ~debug =
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  Coq.Init.(coq_init { debug; load_module; load_plugin })

let exit_notification =
  Lsp.Base.Message.(Notification { method_ = "exit"; params = [] })

let rec lsp_init_loop ~ifn ~ofn ~cmdline ~debug =
  match ifn () with
  | None -> raise Lsp_exit
  | Some msg -> (
    match lsp_init_process ~ofn ~cmdline ~debug msg with
    | Init_effect.Exit -> raise Lsp_exit
    | Init_effect.Loop -> lsp_init_loop ~ifn ~ofn ~cmdline ~debug
    | Init_effect.Success w -> w)

let lsp_main bt coqcorelib coqlib ocamlpath vo_load_path ml_include_path =
  (* Try to be sane w.r.t. \r\n in Windows *)
  Stdlib.set_binary_mode_in stdin true;
  Stdlib.set_binary_mode_out stdout true;

  (* We output to stdout *)
  let ifn () = LIO.read_request stdin in
  (* Set log channels *)
  let ofn = LIO.send_json Format.std_formatter in
  LIO.set_log_fn ofn;
  Fleche.Io.CallBack.set lsp_cb;

  (* IMPORTANT: LSP spec forbids any message from server to client before
     initialize is received *)

  (* Core Coq initialization *)
  let debug = bt || Fleche.Debug.backtraces in
  let root_state = coq_init ~debug in
  let cmdline =
    { Coq.Workspace.CmdLine.coqcorelib
    ; coqlib
    ; ocamlpath
    ; vo_load_path
    ; ml_include_path
    ; args = []
    }
  in

  (* Read JSON-RPC messages and push them to the queue *)
  let rec read_loop () =
    match ifn () with
    | None ->
      (* EOF, push an exit notication to the queue *)
      enqueue_message exit_notification
    | Some msg ->
      enqueue_message msg;
      read_loop ()
  in

  (* Input/output will happen now *)
  try
    (* LSP Server server initialization *)
    let workspaces = lsp_init_loop ~ifn ~ofn ~cmdline ~debug in

    (* Core LSP loop context *)
    let state = { State.root_state; cmdline; workspaces } in

    (* Read workspace state (noop for now) *)
    Cache.read_from_disk ();

    let (_ : Thread.t) =
      Thread.create (fun () -> process_queue ~ofn ~state) ()
    in

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
    "Load Coq.Init.Prelude from $(docv); theories and user-contrib should live \
     there."
  in
  Arg.(
    value & opt string Coq_config.coqlib & info [ "coqlib" ] ~docv:"COQLIB" ~doc)

let coqcorelib =
  let doc = "Path to Coq plugin directories." in
  Arg.(
    value
    & opt string (Filename.concat Coq_config.coqlib "../coq-core/")
    & info [ "coqcorelib" ] ~docv:"COQCORELIB" ~doc)

let ocamlpath =
  let doc = "Path to OCaml's lib" in
  Arg.(
    value & opt (some string) None & info [ "ocamlpath" ] ~docv:"OCAMLPATH" ~doc)

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
      Term.(
        const lsp_main $ bt $ coqcorelib $ coqlib $ ocamlpath $ vo_load_path
        $ ml_include_path))

let main () =
  let ecode = Cmd.eval lsp_cmd in
  exit ecode

let () = main ()
