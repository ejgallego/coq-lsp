open Petanque_json

let prepare_paths () =
  let to_uri file =
    Lang.LUri.of_string file |> Lang.LUri.File.of_uri |> Result.get_ok
  in
  let cwd = Sys.getcwd () in
  let file = Filename.concat cwd "test.v" in
  (to_uri cwd, to_uri file)

let msgs = ref []

let _trace hdr ?extra:_ msg =
  msgs := Format.asprintf "[trace] %s | %s" hdr msg :: !msgs

let _message ~lvl:_ ~message = msgs := message :: !msgs
let dump_msgs () = List.iter (Format.eprintf "%s@\n") (List.rev !msgs)
let id_counter = ref 0

let get_id () =
  incr id_counter;
  !id_counter

(* Client wrap *)
module type Chans = sig
  val ic : in_channel
  val oc : Format.formatter
end

module Wrap (R : Protocol.Request.S) (C : Chans) : sig
  val call : R.Params_.t -> (R.Response_.t, string) Result.t
end = struct
  let read_message ic = Lsp.Io.read_message ic |> Option.get

  let call params =
    let id = get_id () in
    let method_ = R.method_ in
    let params =
      Lsp.Base.Params.Dict
        (Yojson.Safe.Util.to_assoc (R.Params_.to_yojson params))
    in
    let request =
      Lsp.Base.Request.(make ~id ~method_ ~params () |> to_yojson)
    in
    let () = Lsp.Io.send_json C.oc request in
    read_message C.ic |> fun r ->
    Result.bind r (function
      | Lsp.Base.Message.Response (Ok { id = _; result }) ->
        R.Response_.of_yojson result
      | Response (Error { id = _; code = _; message; data = _ }) ->
        Error message
      | Request _ | Notification _ ->
        Error "read loop needs to improve in test case")
end

module S (C : Chans) = struct
  let init =
    let module M = Wrap (Protocol.Init) (C) in
    M.call

  let start =
    let module M = Wrap (Protocol.Start) (C) in
    M.call

  let run_tac =
    let module M = Wrap (Protocol.RunTac) (C) in
    M.call

  let goals =
    let module M = Wrap (Protocol.Goals) (C) in
    M.call

  let premises =
    let module M = Wrap (Protocol.Premises) (C) in
    M.call
end

let run (ic, oc) =
  let open Fleche.Compat.Result.O in
  let debug = false in
  let module S = S (struct
    let ic = ic
    let oc = oc
  end) in
  (* Will this work on Windows? *)
  let root, uri = prepare_paths () in
  let* env = S.init { debug; root } in
  let* st = S.start { env; uri; thm = "rev_snoc_cons" } in
  let* _premises = S.premises { st } in
  let* st = S.run_tac { st; tac = "induction l." } in
  let* st = S.run_tac { st; tac = "-" } in
  let* st = S.run_tac { st; tac = "reflexivity." } in
  let* st = S.run_tac { st; tac = "-" } in
  let* st = S.run_tac { st; tac = "now simpl; rewrite IHl." } in
  let* st = S.run_tac { st; tac = "Qed." } in
  S.goals { st }

let main () =
  let server_out, server_in = Unix.open_process "pet" in
  run (server_out, Format.formatter_of_out_channel server_in)

let check_no_goals = function
  | Error err ->
    Format.eprintf "error: in execution: %s@\n%!" err;
    dump_msgs ();
    129
  | Ok None -> 0
  | Ok (Some _goals) ->
    dump_msgs ();
    Format.eprintf "error: goals remaining@\n%!";
    1

let () =
  let result = main () in
  (* Need to kill the sever... *)
  (* let () = Unix.kill server 9 in *)
  check_no_goals result |> exit
