(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: LSP Controller (Unix)                  *)
(*************************************************************************)

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
    { trace = (fun _hdr ?verbose:_ _msg -> ())
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

(* File *)
module Trace : sig
  val setup : string -> unit
  val cleanup : unit -> unit
end = struct
  let trace_oc = ref None

  (* This is already called under a Mutex, so no need to care about sync here,
     but beware *)
  let log_fn oc hdr obj =
    Format.fprintf oc "[%s] @[%a@]@\n%!" hdr
      (Yojson.Safe.pretty_print ~std:false)
      obj

  let setup file =
    try
      let oc = open_out file in
      let oc_fmt = Format.formatter_of_out_channel oc in
      trace_oc := Some (oc, oc_fmt);
      Lsp.Io.set_log_fn (log_fn oc_fmt)
    with err ->
      let msg = Printexc.to_string err in
      Fleche.Io.Log.trace "Trace.setup"
        "creation of server log file %s failed: @[%s@]" file msg

  (* At exit cleanup *)
  let cleanup () =
    match !trace_oc with
    | None -> ()
    | Some (oc, oc_fmt) ->
      Format.pp_print_flush oc_fmt ();
      Stdlib.flush oc;
      close_out oc
end

let lsp_main bt coqlib findlib_config ocamlpath vo_load_path require_libraries
    delay int_backend lsp_trace lsp_trace_file =
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

  let module CB = Lsp_core.CB (struct
    let ofn = ofn_ntn
  end) in
  let io = CB.cb in
  Fleche.Io.CallBack.set io;

  if lsp_trace then Trace.setup lsp_trace_file;

  (* IMPORTANT: LSP spec forbids any message from server to client before
     initialize is received, [Trace.setup] violates that if there is an error
     when creating the log file. *)

  (* Core Coq initialization *)
  let debug = bt || Fleche.Debug.backtraces in
  let root_state = coq_init ~debug in
  let cmdline =
    { Coq.Workspace.CmdLine.coqlib
    ; findlib_config
    ; ocamlpath
    ; vo_load_path
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
  | Lsp_exit ->
    Trace.cleanup ();
    Fleche.Io.Report.msg ~io ~lvl:Error "[LSP shutdown] EOF\n"
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

let lsp_trace : bool Term.t =
  let doc = "Trace LSP input / output" in
  Arg.(value & flag & info [ "lsp_trace" ] ~docv:"ENABLED" ~doc)

let lsp_trace_file : string Term.t =
  let doc = "Name of the LSP log file $(docv)" in
  let default_file = Format.asprintf "coq_lsp_log_%d.txt" (Unix.getpid ()) in
  Arg.(
    value & opt string default_file
    & info [ "lsp_trace_file" ] ~docv:"TRACE_FILE" ~doc)

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
        const lsp_main $ bt $ coqlib $ findlib_config $ ocamlpath $ vo_load_path
        $ ri_from $ delay $ int_backend $ lsp_trace $ lsp_trace_file))

let main () =
  let ecode = Cmd.eval lsp_cmd in
  exit ecode

let () = main ()
