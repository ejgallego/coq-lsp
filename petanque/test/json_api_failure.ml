open Petanque_json
open Petanque_shell

let prepare_paths () =
  let to_uri file =
    Lang.LUri.of_string file |> Lang.LUri.File.of_uri |> Result.get_ok
  in
  let cwd = Sys.getcwd () in
  let file = Filename.concat cwd "test.v" in
  (to_uri cwd, to_uri file)

let msgs = ref []
let trace ?verbose:_ msg = msgs := Format.asprintf "[trace] %s" msg :: !msgs
let message ~lvl:_ ~message = msgs := message :: !msgs
let dump_msgs () = List.iter (Format.eprintf "%s@\n") (List.rev !msgs)
let extract_st { JAgent.Run_result.st; _ } = st

let run (ic, oc) =
  let open Coq.Compat.Result.O in
  let debug = false in
  let contents = None in
  let module S = Client.S (struct
    let ic = ic
    let oc = oc
    let trace = trace
    let message = message
  end) in
  let r ~st ~tac =
    let opts = None in
    let st = extract_st st in
    S.run { opts; st; tac }
  in
  (* Will this work on Windows? *)
  let root, uri = prepare_paths () in
  let opts = None in
  let* _env = S.set_workspace { debug; root } in
  let* { st; _ } =
    S.start { uri; opts; contents; pre_commands = None; thm = "rev_snoc_cons" }
  in
  let* _premises = S.premises { st } in
  let* st = S.run { opts; st; tac = "induction l." } in
  let* st = r ~st ~tac:"-" in
  (* Introduce an error *)
  (* let* st = r ~st ~tac:"reflexivity." in *)
  let* st = r ~st ~tac:"-" in
  let* st = r ~st ~tac:"now simpl; rewrite IHl." in
  let* st = r ~st ~tac:"Qed." in
  S.goals { st = extract_st st }

let main () =
  let server_out, server_in = Unix.open_process "pet" in
  run (server_out, Format.formatter_of_out_channel server_in)

let check_no_goals = function
  | Error _err ->
    (* errored as expected! *)
    0
  | Ok None ->
    dump_msgs ();
    Format.eprintf "error: we did succeded when we should not@\n%!";
    1
  | Ok (Some _goals) ->
    dump_msgs ();
    Format.eprintf "error: goals remaining@\n%!";
    1

let () =
  let result = main () in
  (* Need to kill the sever... *)
  (* let () = Unix.kill server 9 in *)
  check_no_goals result |> exit
