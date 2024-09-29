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

let findlib_conf = "\ndestdir=\"/static/lib\"path=\"/static/lib\""
let findlib_path = "/static/lib/findlib.conf"

let setup_pseudo_fs () =
  (* '/static' is the default working directory of jsoo *)
  Sys_js.create_file ~name:findlib_path ~content:findlib_conf;
  ()

let setup_std_printers () =
  Sys_js.set_channel_flusher stdout (Fleche.Io.Log.trace "stdout" "%s");
  Sys_js.set_channel_flusher stderr (Fleche.Io.Log.trace "stderr" "%s");
  ()

let post_message (msg : Lsp.Base.Message.t) =
  let json = Lsp.Base.Message.to_yojson msg in
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
  else obj_to_json msg |> Lsp.Base.Message.of_yojson

let on_msg msg =
  match parse_msg msg with
  | Error _ ->
    Lsp.Io.logMessage ~lvl:Lsp.Io.Lvl.Error
      ~message:"Error in JSON RPC Message Parsing"
  | Ok msg ->
    (* Lsp.Io.trace "interrupt_setup" (string_of_bool !interrupt_is_setup); *)
    Lsp_core.enqueue_message msg

let setTimeout cb d = Dom_html.setTimeout cb d

module CB = Controller.Lsp_core.CB (struct
  let ofn n = Lsp.Base.Message.notification n |> post_message
end)

let rec process_queue ~state () =
  match
    Lsp_core.dispatch_or_resume_check ~io:CB.cb ~ofn:post_message ~state
  with
  | None ->
    Fleche.Io.Log.trace "proccess queue" "ended";
    ()
  | Some (Yield state) -> ignore (setTimeout (process_queue ~state) 0.1)
  (* We need to yield so [on_msg] above has the chance to run and add the
     command(s) to the queue. *)
  | Some (Cont state) -> ignore (setTimeout (process_queue ~state) 0.)

let on_init ~io ~root_state ~cmdline ~debug msg =
  match parse_msg msg with
  | Error _ -> ()
  | Ok msg -> (
    match
      Lsp_core.lsp_init_process ~ofn:post_message ~io ~cmdline ~debug msg
    with
    | Lsp_core.Init_effect.Exit -> (* XXX: bind to worker.close () *) ()
    | Lsp_core.Init_effect.Loop -> ()
    | Lsp_core.Init_effect.Success workspaces ->
      Worker.set_onmessage on_msg;
      let default_workspace = Coq.Workspace.default ~debug ~cmdline in
      let state =
        { Lsp_core.State.root_state; cmdline; workspaces; default_workspace }
      in
      ignore (setTimeout (process_queue ~state) 0.1))

let time f x =
  let time = Sys.time () in
  let res = f x in
  let time_new = Sys.time () in
  Format.eprintf "loadfile [dynlink] took: %f seconds%!" (time_new -. time);
  res

let loadfile file =
  let file_js = Filename.remove_extension file ^ ".js" in
  if Sys.file_exists file_js then (
    Format.eprintf "loadfile [eval_js]: %s%!" file;
    let js_code = Sys_js.read_file ~name:file_js in
    let js_code =
      Format.asprintf "(function (globalThis) { @[%s@] })" js_code
    in
    Js.Unsafe.((eval_string js_code : < .. > Js.t -> unit) global))
  else (
    (* Not precompiled *)
    Format.eprintf "loadfile [dynlink]: %s%!" file;
    time Dynlink.loadfile file)

let coq_init ~debug =
  let loader = My_dynload.load_packages ~debug:false ~loadfile in
  let load_module = loadfile in
  let load_plugin = Coq.Loader.plugin_handler (Some loader) in
  (* XXX: Fixme at some point? *)
  let vm, warnings = (false, Some "-vm-compute-disabled") in
  Coq.Init.(coq_init { debug; load_module; load_plugin; vm; warnings })

external coq_vm_trap : unit -> unit = "coq_vm_trap"

(* This code is executed on Worker initialization *)
let main () =
  (* This is needed if dynlink is enabled in 4.03.0 *)
  Sys.interactive := false;

  Coq.Limits.(select Coq);
  Coq.Limits.start ();

  setup_pseudo_fs ();
  setup_std_printers ();

  (* setup_interp (); *)
  coq_vm_trap ();

  Lsp.Io.set_log_fn (fun n -> Lsp.Base.Message.notification n |> post_message);
  let io = CB.cb in
  Fleche.Io.CallBack.set io;

  let stdlib coqlib =
    let unix_path = Filename.concat coqlib "theories" in
    let coq_path = Names.(DirPath.make [ Id.of_string "Stdlib" ]) in
    Loadpath.
      { unix_path; coq_path; implicit = true; has_ml = false; recursive = true }
  in

  let user_contrib coqlib =
    let unix_path = Filename.concat coqlib "user-contrib" in
    let coq_path = Names.DirPath.empty in
    Loadpath.
      { unix_path
      ; coq_path
      ; implicit = false
      ; has_ml = false
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
      ; coqcorelib = "/static/lib/coq-core" (* deprecated upstream *)
      ; findlib_config
      ; ocamlpath
      ; vo_load_path
      ; ml_include_path = []
      ; require_libraries = [ (None, "Coq.Init.Prelude") ]
      ; args = [ "-noinit"; "-boot" ]
      }
  in

  let debug = true in
  let root_state = coq_init ~debug in
  Worker.set_onmessage (on_init ~io ~root_state ~cmdline ~debug);
  ()

let () = main ()
