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

(* let handleRequest json_str = *)
(*   let resp = *)
(*     let cmd = deserialize json_str                     in *)
(*     match cmd with *)
(*     | Result.Error e -> [JsonExn e] *)
(*     | Result.Ok cmd -> *)
(*       let token = Coq.Limits.Token.create () in *)
(*       jscoq_execute ~token cmd; [] *)
(*   in *)
(*   serialize resp *)

(* We do this hack as to use the Coq default loading mechanism that works with
   findlib, but cannot intrument plugin loading *)
(* let handleRequest json_str = *)
(*   if (Mltop.is_ocaml_top ()) then Mltop.remove (); *)
(*   handleRequest json_str *)

(* let handleRequestsFromStdin () = *)
(*   try *)
(*     while true do *)
(*       emit @@ handleRequest @@ Stdlib.read_line () *)
(*     done *)
(*   with End_of_file -> () *)

(* This code is executed on Worker initialization *)
(* Duplicated with coq_lsp_worker.ml , but not using JSOO *)
let _findlib_conf = "\ndestdir=\"/static/lib\"path=\"/static/lib\""
let findlib_path = "/static/lib/findlib.conf"

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

let log_interrupt ~io =
  let lvl, message =
    if not !interrupt_is_setup then
      (* Maybe set one step mode, but usually that's done in the client. *)
      ( Fleche.Io.Level.Error
      , "Interrupt is not setup: Functionality will suffer" )
    else (Fleche.Io.Level.Info, "Interrupt setup: [Control.interrupt] backend")
  in
  Fleche.Io.Report.message_ ~io ~lvl ~message

let on_init ~io ~root_state ~cmdline ~debug msg =
  match parse_message msg with
  | Error err ->
    (* This is called one for interrupt setup *)
    Error err
  | Ok msg -> (
    match
      Lsp_core.lsp_init_process ~ofn:post_message ~io ~cmdline ~debug msg
    with
    | Lsp_core.Init_effect.Exit -> (* XXX: bind to worker.close () *) Ok None
    | Lsp_core.Init_effect.Loop -> Ok None
    | Lsp_core.Init_effect.Success workspaces ->
      log_interrupt ~io;
      (* Worker.set_onmessage (on_msg ~io); *)
      let default_workspace = Coq.Workspace.default ~debug ~cmdline in
      let state =
        { Lsp_core.State.root_state; cmdline; workspaces; default_workspace }
      in
      Ok (Some state))
(* ignore (setTimeout (process_queue ~state) 0.1)) *)

(* Loop *)
let is_init = ref None

let handleRequest ~io ~root_state ~cmdline ~debug json =
  match !is_init with
  | None -> (
    match on_init ~io ~root_state ~cmdline ~debug json with
    | Error _err -> ()
    | Ok None -> ()
    | Ok (Some state) -> is_init := Some state)
  | Some _state -> (
    match parse_message json with
    | Error _ -> ()
    | Ok cmd -> Lsp_core.enqueue_message cmd)

let main () =
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

  let stdlib coqlib =
    let unix_path = Filename.concat coqlib "theories" in
    let coq_path = Names.(DirPath.make [ Id.of_string "Corelib" ]) in
    Loadpath.
      { unix_path
      ; coq_path
      ; installed = true
      ; implicit = true
      ; recursive = true
      }
  in

  let user_contrib coqlib =
    let unix_path = Filename.concat coqlib "user-contrib" in
    let coq_path = Names.DirPath.empty in
    Loadpath.
      { unix_path
      ; coq_path
      ; installed = true
      ; implicit = false
      ; recursive = true
      }
  in

  let cmdline =
    let coqlib = "/static/coqlib" in
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

  let debug = true in
  let root_state = coq_init ~debug in

  (* Specific to WASM, handle new string coming to the worker *)
  let enqueue = handleRequest ~io ~root_state ~cmdline ~debug in
  Callback.register "wacoq_post" enqueue;
  ()

let () = main ()
