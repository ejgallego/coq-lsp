open Lwt
open Lwt.Syntax
open Petanque_shell

let rq_info (r : Lsp.Base.Message.t) =
  match r with
  | Notification { method_; _ } -> Format.asprintf "notification: %s" method_
  | Request { method_; _ } -> Format.asprintf "request: %s" method_
  | Response (Ok { id; _ } | Error { id; _ }) ->
    Format.asprintf "response for: %d" id

let fn = Shell.build_doc

let rec handle_connection ~token ic oc () =
  try
    let* request = Lwt_io.read_line ic in
    let request = Yojson.Safe.from_string request in
    match Lsp.Base.Message.of_yojson request with
    | Error err ->
      (* error in Json message *)
      let* () = Logs_lwt.info (fun m -> m "Error: %s" err) in
      handle_connection ~token ic oc ()
    | Ok request -> (
      (* everything is fine up to JSON-RPC level *)
      let* () = Logs_lwt.info (fun m -> m "Received: %s" (rq_info request)) in
      (* request could be a notification, so maybe we don't have to do a
         reply! *)
      match Interp_shell.interp ~fn ~token request with
      | None -> handle_connection ~token ic oc ()
      | Some reply ->
        let* () = Logs_lwt.info (fun m -> m "Sent reply") in
        let* () =
          Lwt_io.fprintl oc
            (Yojson.Safe.to_string (Lsp.Base.Message.to_yojson reply))
        in
        handle_connection ~token ic oc ())
  with End_of_file -> return ()

let accept_connection ~token conn =
  let fd, _ = conn in
  let ic = Lwt_io.of_fd ~mode:Lwt_io.Input fd in
  let oc = Lwt_io.of_fd ~mode:Lwt_io.Output fd in
  let* () = Logs_lwt.info (fun m -> m "New connection") in
  Lwt.on_failure (handle_connection ~token ic oc ()) (fun e ->
      Logs.err (fun m -> m "%s" (Printexc.to_string e)));
  return ()

let create_socket ~address ~port ~backlog =
  let open Lwt_unix in
  let sock = socket PF_INET SOCK_STREAM 0 in
  (* It is sometimes more convenient to allow pet-server to shadow a kind of
     crashed one, so we allow to rebind the socket. It could be convenient at
     some point to guard this over a command-line flag *)
  let () = setsockopt sock SO_REUSEADDR true in
  let () = setsockopt sock SO_REUSEPORT true in
  ( bind sock @@ ADDR_INET (Unix.inet_addr_of_string address, port) |> fun x ->
    ignore x );
  listen sock backlog;
  sock

let create_server ~token sock =
  let rec serve () =
    let* conn = Lwt_unix.accept sock in
    let* () = accept_connection ~token conn in
    serve ()
  in
  serve

let log_error err =
  let message = Petanque.Agent.Error.to_string err in
  Format.eprintf "Error in --root option: %s@\n%!" message
(* Logs_lwt.info (fun m -> m "%s" message) *)

let pet_main debug roots address port backlog =
  Coq.Limits.start ();
  let token = Coq.Limits.Token.create () in
  let () = Logs.set_reporter (Logs.format_reporter ()) in
  let () = Logs.set_level (Some Logs.Info) in
  let sock = create_socket ~address ~port ~backlog in
  let serve = create_server ~token sock in
  (* EJGA: pet-server should handle this at some point *)
  (* Petanque.Shell.trace_ref := trace_notification; *)
  (* Petanque.Shell.message_ref := message_notification); *)
  Result.iter_error log_error (Shell.init_agent ~token ~debug ~roots);
  Lwt_main.run @@ serve ()

open Cmdliner

let address =
  let doc = "address to listen to" in
  Arg.(
    value & opt string "127.0.0.1"
    & info [ "a"; "address" ] ~docv:"ADDRESS" ~doc)

let port =
  let doc = "port to listen to" in
  Arg.(value & opt int 8765 & info [ "p"; "port" ] ~docv:"PORT" ~doc)

let backlog =
  let doc = "socket backlog" in
  Arg.(value & opt int 10 & info [ "b"; "backlog" ] ~docv:"BACKLOG" ~doc)

let pet_cmd : unit Cmd.t =
  let doc = "Petanque Server" in
  let man =
    [ `S "DESCRIPTION"
    ; `P "Launch a petanque server to interact with Coq"
    ; `S "USAGE"
    ; `P
        "See\n\
        \    the\n\
        \  documentation on the project's webpage for more information"
    ]
  in
  let version = Fleche.Version.server in
  let pet_term =
    Term.(
      const pet_main $ Coq.Args.debug $ Coq.Args.roots $ address $ port
      $ backlog)
  in
  Cmd.(v (Cmd.info "pet" ~version ~doc ~man) pet_term)

let main () =
  let ecode = Cmd.eval pet_cmd in
  exit ecode

let () = main ()
