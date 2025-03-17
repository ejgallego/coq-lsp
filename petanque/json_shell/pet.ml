(* json rpc server *)
module Lsp = Fleche_lsp
open Petanque_shell

let use_http_headers = ref true

let read_json inc =
  match Yojson.Safe.from_channel inc with
  | json -> Ok json
  | exception Yojson.Json_error err -> Error err

let read_message inc =
  if !use_http_headers then Lsp.Io.read_message inc
  else
    try
      match read_json inc with
      | Error err -> Some (Error err)
      | Ok json -> Some (Lsp.Base.Message.of_yojson json)
    with End_of_file -> None

let send_message msg =
  if !use_http_headers then (
    Lsp.Io.send_message Format.std_formatter msg;
    Format.pp_print_flush Format.std_formatter ())
  else
    let msg = Lsp.Base.Message.to_yojson msg in
    Format.fprintf Format.std_formatter "@[%s@]@\n%!"
      (Yojson.Safe.to_string ?std:None msg)
(* Format.fprintf Format.std_formatter "@[%a@]@\n%!" Yojson.Safe.pretty_print
   msg *)

let fn = Shell.build_doc

let interp ~token request =
  match Interp_shell.interp ~fn ~token request with
  | None -> ()
  | Some message -> send_message message

let rec loop ~token : unit =
  match read_message stdin with
  | None -> () (* EOF *)
  | Some (Ok request) ->
    interp ~token request;
    loop ~token
  | Some (Error err) ->
    Format.eprintf "@[error: %s@\n@]%!" err;
    loop ~token

let trace_notification hdr ?verbose msg =
  let message = Format.asprintf "[%s] %s" hdr msg in
  let notification = Lsp.Base.mk_logTrace ~message ~verbose in
  send_message (Lsp.Base.Message.Notification notification)

let message_notification ~lvl ~message =
  let notification = Lsp.Base.mk_logMessage ~lvl ~message in
  send_message (Lsp.Base.Message.Notification notification)

let trace_enabled = true

let log_error err =
  let message = Petanque.Agent.Error.to_string err in
  message_notification ~lvl:Fleche.Io.Level.Error ~message

let pet_main debug roots http_headers =
  Coq.Limits.start ();
  if trace_enabled then (
    Shell.trace_ref := trace_notification;
    Shell.message_ref := message_notification);
  let token = Coq.Limits.Token.create () in
  Result.iter_error log_error (Shell.init_agent ~token ~debug ~roots);
  use_http_headers := http_headers;
  loop ~token

open Cmdliner

let http_headers : bool Term.t =
  let docv = "{yes|no}" in
  let opts = [ ("yes", true); ("no", false) ] in
  let absent = "yes" in
  let doc =
    "whether http-headers CONTENT-LENGHT are used in the JSON-RPC encoding"
  in
  Arg.(
    value & opt (enum opts) true & info [ "http_headers" ] ~docv ~doc ~absent)

let pet_cmd : unit Cmd.t =
  let doc = "Petanque Coq Environment" in
  let man =
    [ `S "DESCRIPTION"
    ; `P "Petanque Coq Environment"
    ; `S "USAGE"
    ; `P "See the documentation on the project's webpage for more information"
    ]
  in
  let version = Fleche.Version.server in
  let pet_term =
    Term.(const pet_main $ Coq.Args.debug $ Coq.Args.roots $ http_headers)
    (* const pet_main $ roots $ display $ debug $ plugins $ file $ coqlib *)
    (* $ coqcorelib $ ocamlpath $ rload_path $ load_path $ rifrom) *)
  in
  Cmd.(v (Cmd.info "pet" ~version ~doc ~man) pet_term)

let main () =
  let ecode = Cmd.eval pet_cmd in
  exit ecode

let () = main ()
