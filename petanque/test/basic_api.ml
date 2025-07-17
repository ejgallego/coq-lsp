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

let trace hdr ?verbose:_ msg =
  msgs := Format.asprintf "[trace] %s | %s" hdr msg :: !msgs

let message ~lvl:_ ~message = msgs := message :: !msgs
let dump_msgs () = List.iter (Format.eprintf "%s@\n") (List.rev !msgs)

let init ~token =
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
  Shell.build_doc ~token ~uri

let extract_st { Agent.Run_result.st; _ } = st

let snoc_test ~token ~doc =
  let open Coq.Compat.Result.O in
  let r ~st ~tac =
    let st = extract_st st in
    Agent.run ~token ~st ~tac ()
  in
  let* { st; _ } = Agent.start ~token ~doc ~thm:"rev_snoc_cons" () in
  let* _premises = Agent.premises ~token ~st in
  let* st = Agent.run ~token ~st ~tac:"induction l." () in
  let h1 = Agent.State.hash st.st in
  let* st = r ~st ~tac:"idtac." in
  let h2 = Agent.State.hash st.st in
  assert (Int.equal h1 h2);
  let* st = r ~st ~tac:"-" in
  let* st = r ~st ~tac:"reflexivity." in
  let h3 = Agent.State.hash st.st in
  (* Fails in 8.18 *)
  assert (not (Int.equal h1 h3));
  (* Fails in 8.17 *)
  (* assert (Int.equal h1 h3); *)
  (* ast test *)
  let* _ast1 = Agent.ast ~token ~st:st.st ~text:"Check (fun x => x)." () in
  let* _ast2 = Agent.ast_at_pos ~doc ~point:(15, 3) () in
  let* st = r ~st ~tac:"-" in
  let* st = r ~st ~tac:"now simpl; rewrite IHl." in
  let* st = r ~st ~tac:"Qed." in
  Agent.goals ~token ~st:(extract_st st)

let finished_stack_test ~token ~doc =
  let open Coq.Compat.Result.O in
  let r ~st ~tac =
    let st = extract_st st in
    Agent.run ~token ~st ~tac ()
  in
  let* { st; _ } = Agent.start ~token ~doc ~thm:"deepBullet" () in
  let* st = Agent.run ~token ~st ~tac:"split." () in
  let* st = r ~st ~tac:"-" in
  let* st = r ~st ~tac:"now reflexivity." in
  let* st = r ~st ~tac:"-" in
  let* st = r ~st ~tac:"split." in
  let* st = r ~st ~tac:"+" in
  let* st = r ~st ~tac:"now reflexivity." in
  let* st = r ~st ~tac:"+" in
  let* { st; proof_finished; _ } = r ~st ~tac:"now reflexivity." in
  (* Check that we properly detect no goals with deep stacks. *)
  assert proof_finished;
  let* st = Agent.run ~token ~st ~tac:"Qed." () in
  Agent.goals ~token ~st:(extract_st st)

let multi_shot_test ~token ~doc =
  let open Coq.Compat.Result.O in
  let* { st; _ } = Agent.start ~token ~doc ~thm:"rev_snoc_cons" () in
  let* st =
    Agent.run ~token ~st
      ~tac:"induction l. idtac. - reflexivity. - now simpl; rewrite IHl. Qed."
      ()
  in
  Agent.goals ~token ~st:(extract_st st)

let fake_start_test ~token ~doc =
  match Agent.start ~token ~doc ~thm:"foo" () with
  | Ok _ ->
    Error (Agent.Error.make_request (System "start on foo should have failed"))
  | Error _ -> Ok None

let main () =
  let open Coq.Compat.Result.O in
  let token = Coq.Limits.create_atomic () in
  let* doc = init ~token in
  let* g1 = snoc_test ~token ~doc in
  let* g2 = finished_stack_test ~token ~doc in
  let* g3 = multi_shot_test ~token ~doc in
  let* g4 = fake_start_test ~token ~doc in
  Ok [ g1; g2; g3; g4 ]

let max = List.fold_left max min_int

let check_no_goals = function
  | Error Request.Error.{ payload = err; _ } ->
    Format.eprintf "error: in execution: %s@\n%!" (Agent.Error.to_string err);
    dump_msgs ();
    129
  | Ok glist ->
    List.map
      (function
        | None -> 0
        | Some _goals ->
          dump_msgs ();
          Format.eprintf "error: goals remaining@\n%!";
          1)
      glist
    |> max

let () = main () |> check_no_goals |> exit
