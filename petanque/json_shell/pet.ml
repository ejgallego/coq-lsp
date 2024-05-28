(* json rpc server *)
open Petanque_json

let interp ~token request =
  match Interp.interp ~token request with
  | None -> ()
  | Some response ->
    Lsp.Io.send_json Format.std_formatter response;
    Format.pp_print_flush Format.std_formatter ()

let rec loop ~token : unit =
  match Lsp.Io.read_message stdin with
  | None -> () (* EOF *)
  | Some (Ok request) ->
    interp ~token request;
    loop ~token
  | Some (Error err) ->
    Format.eprintf "@[error: %s@\n@]%!" err;
    loop ~token

let trace_notification hdr ?extra msg =
  let module M = Protocol.Trace in
  let method_ = M.method_ in
  let message = Format.asprintf "[%s] %s" hdr msg in
  let params = { M.Params.message; verbose = extra } in
  let params = M.Params.to_yojson params |> Yojson.Safe.Util.to_assoc in
  let notification =
    Lsp.Base.Notification.(make ~method_ ~params () |> to_yojson)
  in
  Lsp.Io.send_json Format.std_formatter notification

let message_notification ~lvl ~message =
  let module M = Protocol.Message in
  let method_ = M.method_ in
  let type_ = Fleche.Io.Level.to_int lvl in
  let params = M.Params.({ type_; message } |> to_yojson) in
  let params = Yojson.Safe.Util.to_assoc params in
  let notification =
    Lsp.Base.Notification.(make ~method_ ~params () |> to_yojson)
  in
  Lsp.Io.send_json Format.std_formatter notification

(* XXX: Flèche LSP backend already handles the conversion at the protocol
   level *)
let uri_of_string_exn uri =
  Lang.LUri.of_string uri |> Lang.LUri.File.of_uri |> Result.get_ok

let trace_enabled = true

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
