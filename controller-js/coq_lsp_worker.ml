(* Coq JavaScript API.
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2023 Shachar Itzhaky, Technion
 * Copyright (C) 2019-2023 Emilio J. Gallego Arias, INRIA
 * LICENSE: GPLv3+
 *
 * We provide a message-based asynchronous API for communication with
 * Coq.
 *)

module U = Yojson.Safe.Util
module LIO = Lsp.Io
module LSP = Lsp.Base
open Js_of_ocaml
open Controller

let rec obj_to_json (cobj : < .. > Js.t) : Yojson.Safe.t =
  let open Js in
  let open Js.Unsafe in
  let typeof_cobj = to_string (typeof cobj) in
  match typeof_cobj with
  | "string" -> `String (to_string @@ coerce cobj)
  | "boolean" -> `Bool (to_bool @@ coerce cobj)
  | "number" -> `Int (int_of_float @@ float_of_number @@ coerce cobj)
  | _ ->
    if instanceof cobj array_empty then
      `List Array.(to_list @@ map obj_to_json @@ to_array @@ coerce cobj)
    else if instanceof cobj Typed_array.arrayBuffer then
      `String (Typed_array.String.of_arrayBuffer @@ coerce cobj)
    else if instanceof cobj Typed_array.uint8Array then
      `String (Typed_array.String.of_uint8Array @@ coerce cobj)
    else
      let json_string = Js.to_string (Json.output cobj) in
      Yojson.Safe.from_string json_string

let rec json_to_obj (cobj : < .. > Js.t) (json : Yojson.Safe.t) : < .. > Js.t =
  let open Js.Unsafe in
  let ofresh j = json_to_obj (obj [||]) j in
  match json with
  | `Bool b -> coerce @@ Js.bool b
  | `Null -> pure_js_expr "null"
  | `Assoc l ->
    List.iter (fun (p, js) -> set cobj p (ofresh js)) l;
    cobj
  | `List l -> Array.(Js.array @@ map ofresh (of_list l))
  | `Float f -> coerce @@ Js.number_of_float f
  | `String s -> coerce @@ Js.string s
  | `Int m -> coerce @@ Js.number_of_float (float_of_int m)
  | `Intlit s -> coerce @@ Js.number_of_float (float_of_string s)
  | `Tuple t -> Array.(Js.array @@ map ofresh (of_list t))
  | `Variant (_, _) -> pure_js_expr "undefined"

let findlib_conf = "\ndestdir=\"/lib\"path=\"/lib\""

let lib_fs ~prefix:_ ~path =
  match path with
  | "findlib.conf" -> Some findlib_conf
  | _ -> None

let setup_pseudo_fs () =
  (* '/static' is the default working directory of jsoo *)
  Sys_js.unmount ~path:"/static";
  Sys_js.mount ~path:"/lib/" lib_fs

let setup_std_printers () =
  (* XXX Convert to logTrace? *)
  (* Sys_js.set_channel_flusher stdout (fun msg -> post_answer (Log (Notice,
     Pp.str @@ "stdout: " ^ msg))); *)
  (* Sys_js.set_channel_flusher stderr (fun msg -> post_answer (Log (Notice,
     Pp.str @@ "stderr: " ^ msg))); *)
  ()

let post_message (json : Yojson.Safe.t) =
  let js = json_to_obj (Js.Unsafe.obj [||]) json in
  Worker.post_message js

type opaque

external interrupt_setup : opaque (* Uint32Array *) -> unit = "interrupt_setup"

let interrupt_is_setup = ref false

let parse_msg msg =
  if Js.instanceof msg Js.array_length then (
    let _method_ = Js.array_get msg 0 in
    let handle = Js.array_get msg 1 |> Obj.magic in
    interrupt_setup handle;
    interrupt_is_setup := true;
    Error "processed interrupt_setup")
  else obj_to_json msg |> Lsp.Base.Message.from_yojson

let on_msg msg =
  match parse_msg msg with
  | Error _ ->
    Lsp.Io.logMessage ~lvl:1 ~message:"Error in JSON RPC Message Parsing"
  | Ok msg ->
    Lsp.Io.trace "interrupt_setup" (string_of_bool !interrupt_is_setup);
    Lsp_core.enqueue_message msg

let setTimeout cb d = Dom_html.setTimeout cb d

let io_cb =
  Fleche.Io.CallBack.
    { trace = Lsp.Io.trace
    ; message = Lsp.Io.logMessage
    ; diagnostics =
        (fun ~uri ~version diags ->
          Lsp.JLang.mk_diagnostics ~uri ~version diags |> post_message)
    ; fileProgress =
        (fun ~uri ~version progress ->
          Lsp.JFleche.mk_progress ~uri ~version progress |> post_message)
    }

let rec process_queue ~state () =
  match
    Lsp_core.dispatch_or_resume_check ~io:io_cb ~ofn:post_message ~state
  with
  | None ->
    LIO.trace "proccess queue" "ended";
    ()
  | Some (Yield state) -> ignore (setTimeout (process_queue ~state) 0.1)
  | Some (Cont state) -> process_queue ~state ()

let on_init ~root_state ~cmdline ~debug msg =
  match parse_msg msg with
  | Error _ -> ()
  | Ok msg -> (
    match Lsp_core.lsp_init_process ~ofn:post_message ~cmdline ~debug msg with
    | Lsp_core.Init_effect.Exit -> (* XXX: bind to worker.close () *) ()
    | Lsp_core.Init_effect.Loop -> ()
    | Lsp_core.Init_effect.Success workspaces ->
      Worker.set_onmessage on_msg;
      let state = { Lsp_core.State.root_state; cmdline; workspaces } in
      ignore (setTimeout (process_queue ~state) 0.1))

let coq_init ~debug =
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  Coq.Init.(coq_init { debug; load_module; load_plugin })

external coq_vm_trap : unit -> unit = "coq_vm_trap"

(* This code is executed on Worker initialization *)
let main () =
  (* This is needed if dynlink is enabled in 4.03.0 *)
  Sys.interactive := false;

  setup_pseudo_fs ();
  setup_std_printers ();

  (* setup_interp (); *)
  coq_vm_trap ();

  Lsp.Io.set_log_fn post_message;
  Fleche.Io.CallBack.set io_cb;

  let cmdline =
    Coq.Workspace.CmdLine.
      { coqlib = "/lib/coq"
      ; coqcorelib = "/lib/coq"
      ; ocamlpath = Some "/lib"
      ; vo_load_path = []
      ; ml_include_path = []
      ; args = [ "-noinit" ]
      }
  in
  let debug = true in
  let root_state = coq_init ~debug in
  Worker.set_onmessage (on_init ~root_state ~cmdline ~debug);
  ()

let () = main ()
