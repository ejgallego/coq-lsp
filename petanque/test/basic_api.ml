open Petanque
open Petanque_shell

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
  Shell.trace_ref := trace;
  Shell.message_ref := message;
  (* Will this work on Windows? *)
  let open Coq.Compat.Result.O in
  let _ : _ Result.t = Shell.init_agent ~token ~debug ~roots:[] in
  (* Twice to test for #766 *)
  let root, uri = prepare_paths () in
  let* () = Shell.set_workspace ~token ~debug ~root in
  let* () = Shell.set_workspace ~token ~debug ~root in
  (* Careful to call [build_doc] before we have set an environment! [pet] and
     [pet-server] are careful to always set a default one *)
  let* doc = Shell.build_doc ~token ~uri in
  Agent.start ~token ~doc ~thm:"rev_snoc_cons" ()

let extract_st { Agent.Run_result.st; _ } = st

let main () =
  let open Coq.Compat.Result.O in
  let token = Coq.Limits.create_atomic () in
  let r ~st ~tac =
    let st = extract_st st in
    Agent.run ~token ~st ~tac ()
  in
  let* { st; _ } = start ~token in
  let* _premises = Agent.premises ~token ~st in
  let* st = Agent.run ~token ~st ~tac:"induction l." () in
  let h1 = Agent.State.hash st.st in
  let* st = r ~st ~tac:"idtac." in
  let h2 = Agent.State.hash st.st in
  assert (Int.equal h1 h2);
  let* st = r ~st ~tac:"-" in
  let* st = r ~st ~tac:"reflexivity." in
  let h3 = Agent.State.hash st.st in
  assert (not (Int.equal h1 h3));
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
