(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2018-2025 Shachar Itzhaky Technion -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: LSP Controller (Javascript)            *)
(*************************************************************************)

let e cc =
  Format.kfprintf
    (fun fmt -> Format.fprintf fmt "@\n%!")
    Format.err_formatter cc

external emit : string -> unit = "wacoq_emit" (* implemented in `core.ts` *)

(* XXX: We don't set the content-length headers *)
let json_from_string json =
  match Yojson.Safe.from_string json with
  | exception Yojson.Json_error err -> Error err
  | r -> Ok r

let parse_message (json : string) =
  let open Coq.Compat.Result.O in
  let* json = json_from_string json in
  Fleche_lsp.Base.Message.of_yojson json

let post_message (msg : Fleche_lsp.Base.Message.t) =
  let msg = Yojson.Safe.to_string (Fleche_lsp.Base.Message.to_yojson msg) in
  emit msg

(* This code is executed on Worker initialization *)
(* Duplicated with coq_lsp_worker.ml , but not using JSOO *)
let findlib_conf = "\ndestdir=\"/static/lib\"path=\"/static/lib\""
let findlib_path = "/lib/findlib.conf"

let coq_init ~debug =
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  (* XXX: Fixme at some point? *)
  let vm, warnings = (false, Some "-vm-compute-disabled") in
  Coq.Init.(coq_init { debug; load_module; load_plugin; vm; warnings })

(* Start of controller core *)
open Controller

module CB = Lsp_core.CB (struct
  let ofn n = Fleche_lsp.Base.Message.notification n |> post_message
end)

let interrupt_is_setup = ref false

let _log_interrupt ~io =
  let lvl, message =
    if not !interrupt_is_setup then
      (* Maybe set one step mode, but usually that's done in the client. *)
      ( Fleche.Io.Level.Error
      , "Interrupt is not setup: Functionality will suffer" )
    else (Fleche.Io.Level.Info, "Interrupt setup: [Control.interrupt] backend")
  in
  Fleche.Io.Report.message_ ~io ~lvl ~message

let on_init ~io ~root_state ~cmdline ~debug cmd =
  match Lsp_core.lsp_init_process ~ofn:post_message ~io ~cmdline ~debug cmd with
  | Lsp_core.Init_effect.Exit -> (* XXX: bind to worker.close () *) None
  | Lsp_core.Init_effect.Loop -> None
  | Lsp_core.Init_effect.Success workspaces ->
    (* log_interrupt ~io; *)
    (* Worker.set_onmessage (on_msg ~io); *)
    let default_workspace = Coq.Workspace.default ~debug ~cmdline in
    let state =
      { Lsp_core.State.root_state; cmdline; workspaces; default_workspace }
    in
    Some state

(* Sched *)
let rec sched ~io ~state =
  match Lsp_core.dispatch_or_resume_check ~io ~ofn:post_message ~state with
  | Some (Cont state) -> sched ~io ~state
  | Some (Yield state) -> Some state
  | None -> None

(* TODO: properly answer with JSON-RPC Error message and code *)
let parse_error _ = ()

(* Loop *)
let handle_st = ref None

let handleCmd ~io cmd ~root_state ~cmdline ~debug =
  match !handle_st with
  | None -> (
    (* Not initialized *)
    match on_init ~io ~root_state ~cmdline ~debug cmd with
    | None -> ()
    | Some state -> handle_st := Some state)
  | Some _ -> Lsp_core.enqueue_message cmd

let handleRequest ~io ~root_state ~cmdline ~debug json : unit =
  match parse_message json with
  | Error err -> parse_error err
  | Ok cmd -> handleCmd ~io ~root_state ~cmdline ~debug cmd

let main () =
  e "boot: phase 1";

  (* Remove when we have the filesystem *)
  Coq.Compat.Ocaml_414.Out_channel.with_open_bin findlib_path (fun oc ->
      Stdlib.output_string oc findlib_conf);

  let () = Array.iter (Format.eprintf "%s@\n") (Sys.readdir "/") in

  let () = Array.iter (Format.eprintf "%s@\n") (Sys.readdir "/lib") in

  e "boot: phase 2";
  (* This is needed if dynlink is enabled in 4.03.0 *)
  Sys.interactive := false;

  Coq.Limits.(select Coq);
  Coq.Limits.start ();

  (* XXX: WASM *)
  (* setup_pseudo_fs (); *)
  (* setup_std_printers (); *)

  (* setup_interp (); *)

  (* XXX: WASM *)
  (* rocq_vm_trap (); *)

  (* Review *)
  let io = CB.cb in
  Fleche.Io.CallBack.set io;

  e "boot: phase 3";
  let stdlib coqlib =
    let unix_path = Filename.concat coqlib "theories" in
    let coq_path = Names.(DirPath.make [ Id.of_string "Corelib" ]) in
    Loadpath.{ unix_path; coq_path; implicit = true; recursive = true }
  in

  let user_contrib coqlib =
    let unix_path = Filename.concat coqlib "user-contrib" in
    let coq_path = Names.DirPath.empty in
    Loadpath.{ unix_path; coq_path; implicit = false; recursive = true }
  in

  let cmdline =
    let coqlib = "/static/rocqlib" in
    let findlib_config = Some findlib_path in
    let ocamlpath = [] in
    let vo_load_path = List.map (fun f -> f coqlib) [ stdlib; user_contrib ] in
    Coq.Workspace.CmdLine.
      { coqlib
      ; findlib_config
      ; ocamlpath
      ; vo_load_path
      ; require_libraries = [ (None, "Corelib.Init.Prelude") ]
      ; args = [ "-noinit"; "-boot" ]
      }
  in

  let debug = false in
  e "boot: phase 4";
  let root_state = coq_init ~debug in

  e "boot: phase 5";
  (* Specific to WASM, handle new string coming to the worker *)
  let enqueue = handleRequest ~io ~root_state ~cmdline ~debug in
  let sched () =
    match !handle_st with
    | None -> () (* XXX check this is LSP-compliant *)
    | Some state -> handle_st := sched ~io ~state
  in
  Callback.register "wacoq_post" enqueue;
  Callback.register "wacoq_idle" sched;
  e "boot: phase 6";
  ()

let () = main ()
