open Petanque

let prepare_paths () =
  let to_uri file =
    Lang.LUri.of_string file |> Lang.LUri.File.of_uri |> Result.get_ok
  in
  let cwd = Sys.getcwd () in
  let file = Filename.concat cwd "test.v" in
  (to_uri cwd, to_uri file)

let msgs = ref []

let trace hdr ?extra:_ msg =
  msgs := Format.asprintf "[trace] %s | %s" hdr msg :: !msgs

let message ~lvl:_ ~message = msgs := message :: !msgs
let dump_msgs () = List.iter (Format.eprintf "%s@\n") (List.rev !msgs)

let start ~token =
  let debug = false in
  Petanque.Agent.trace_ref := trace;
  Petanque.Agent.message_ref := message;
  (* Will this work on Windows? *)
  let open Coq.Compat.Result.O in
  let root, uri = prepare_paths () in
  (* Twice to test for #766 *)
  let* _env = Agent.init ~token ~debug ~root in
  let* env = Agent.init ~token ~debug ~root in
  Agent.start ~token ~env ~uri ~thm:"rev_snoc_cons"

let extract_st (st : _ Agent.Run_result.t) =
  match st with
  | Proof_finished st | Current_state st -> st

let main () =
  let open Coq.Compat.Result.O in
  let token = Coq.Limits.create_atomic () in
  let r ~st ~tac =
    let st = extract_st st in
    Agent.run_tac ~token ~st ~tac
  in
  let* st = start ~token in
  let* _premises = Agent.premises ~token ~st in
  let* st = Agent.run_tac ~token ~st ~tac:"induction l." in
  let* st = r ~st ~tac:"-" in
  let* st = r ~st ~tac:"reflexivity." in
  let* st = r ~st ~tac:"-" in
  let* st = r ~st ~tac:"now simpl; rewrite IHl." in
  let* st = r ~st ~tac:"Qed." in
  Agent.goals ~token ~st:(extract_st st)

let check_no_goals = function
  | Error err ->
    Format.eprintf "error: in execution: %s@\n%!" (Agent.Error.to_string err);
    dump_msgs ();
    129
  | Ok None -> 0
  | Ok (Some _goals) ->
    dump_msgs ();
    Format.eprintf "error: goals remaining@\n%!";
    1

let () = main () |> check_no_goals |> exit
