(* json rpc server *)
open Petanque_json

let interp ~token request =
  match Interp.interp ~token request with
  | None -> ()
  | Some response ->
    Lsp.Io.send_json Format.std_formatter response;
    Format.pp_print_flush Format.std_formatter ()

let rec loop ~token : unit =
  match Lsp.Io.read_request stdin with
  | None -> () (* EOF *)
  | Some (Ok request) ->
    interp ~token request;
    loop ~token
  | Some (Error err) ->
    Format.eprintf "@[error: %s@\n@]%!" err;
    loop ~token

let trace_notification hdr ?extra msg =
  let method_ = Protocol.Trace.method_ in
  let message = Format.asprintf "[%s] %s" hdr msg in
  let params = { Protocol.Trace.Params.message; verbose = extra } in
  let params = Protocol.Trace.Params.to_yojson params in
  let notification = Lsp.Base.mk_notification ~method_ ~params in
  Lsp.Io.send_json Format.std_formatter notification

let message_notification ~lvl ~message =
  let method_ = Protocol.Message.method_ in
  let type_ = Fleche.Io.Level.to_int lvl in
  let params = { Protocol.Message.Params.type_; message } in
  let params = Protocol.Message.Params.to_yojson params in
  let notification = Lsp.Base.mk_notification ~method_ ~params in
  Lsp.Io.send_json Format.std_formatter notification

(* XXX: Flèche LSP backend already handles the conversion at the protocol
   level *)
let uri_of_string_exn uri =
  Lang.LUri.of_string uri |> Lang.LUri.File.of_uri |> Result.get_ok

let trace_enabled = false

let pet_main debug roots =
  Coq.Limits.start ();
  (* Don't trace for now *)
  if trace_enabled then (
    Petanque.Agent.trace_ref := trace_notification;
    Petanque.Agent.message_ref := message_notification);
  let token = Coq.Limits.Token.create () in
  let () =
    match roots with
    | [] -> ()
    | [ root ] | root :: _ -> (
      let root = uri_of_string_exn root in
      match Petanque.Agent.init ~token ~debug ~root with
      | Ok env ->
        (* hack until we fix the stuff *)
        let _ : Yojson.Safe.t = JAgent.Env.to_yojson env in
        ()
      | Error err ->
        Format.eprintf "Error: %s@\n%!" (Petanque.Agent.Error.to_string err))
  in
  loop ~token

open Cmdliner

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
    Term.(const pet_main $ Coq.Args.debug $ Coq.Args.roots)
    (* const pet_main $ roots $ display $ debug $ plugins $ file $ coqlib *)
    (* $ coqcorelib $ ocamlpath $ rload_path $ load_path $ rifrom) *)
  in
  Cmd.(v (Cmd.info "pet" ~version ~doc ~man) pet_term)

let main () =
  let ecode = Cmd.eval pet_cmd in
  exit ecode

let () = main ()
