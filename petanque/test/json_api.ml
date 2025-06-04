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

let check_search { JAgent.Run_result.feedback; _ } n =
  let nfb = List.length feedback in
  if Int.equal nfb n then ()
  else (
    Format.eprintf "error in search, got %d , expected %d@\n%!" nfb n;
    assert false)

let pp_offset fmt (bp, ep) = Format.fprintf fmt "(%d,%d)" bp ep

let pp_res_str =
  Coq.Compat.Result.pp Format.pp_print_string Format.pp_print_string

let pp_info fmt info =
  let { Petanque.Agent.Premise.Info.kind; range = _; offset; raw_text } =
    info
  in
  Format.fprintf fmt "kind = %s;@ offset = %a;@ raw_text = %a" kind pp_offset
    offset pp_res_str raw_text

let pp_premise fmt { Petanque.Agent.Premise.full_name; file; info } =
  Format.(
    fprintf fmt "@[{ name = %s;@ file = %s;@ %a}@]@\n" full_name file
      (Coq.Compat.Result.pp pp_info pp_print_string)
      info)

let print_premises = false

let pp_toc fmt (name, ast_info) =
  let pp_ast_info fmt ast_info =
    let ast_info =
      Option.map (List.map JAgent.Lang.Ast.Info.to_yojson) ast_info
    in
    Format.fprintf fmt "@[%a@]"
      Format.(pp_print_option (pp_print_list Yojson.Safe.pp))
      ast_info
  in
  Format.(
    fprintf fmt "@[{ name = %s; ast_info = @[%a@] @]" name pp_ast_info ast_info)

let print_toc = false

let run (ic, oc) =
  let open Coq.Compat.Result.O in
  let debug = false in
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
  let* () = S.set_workspace { debug; root } in
  let* { st; _ } =
    S.start { uri; opts = None; pre_commands = None; thm = "rev_snoc_cons" }
  in
  (* Check get_at_pos works, note that LSP positions start at 0 ! *)
  let position = Lang.Point.{ line = 13; character = 0; offset = -1 } in
  let* st' = S.get_state_at_pos { uri; opts = None; position } in
  let* eq = S.state_equal { kind = None; st1 = st; st2 = st'.st } in
  assert eq;
  let* premises = S.premises { st } in
  (if print_premises then
     Format.(eprintf "@[%a@]@\n%!" (pp_print_list pp_premise) premises));
  let* toc = S.toc { uri } in
  (if print_toc then Format.(eprintf "@[%a@]@\n%!" (pp_print_list pp_toc) toc));
  let* st = S.run { opts = None; st; tac = "induction l." } in
  let* h1 = S.state_hash { st = st.st } in
  let* h1_p = S.state_proof_hash { st = st.st } in
  let* st = r ~st ~tac:"idtac." in
  let* h2 = S.state_hash { st = st.st } in
  let* h2_p = S.state_proof_hash { st = st.st } in
  assert (Int.equal h1 h2);
  assert (Option.equal Int.equal h1_p h2_p);
  let* st = r ~st ~tac:"-" in
  let* st = r ~st ~tac:"reflexivity." in
  let* _h3 = S.state_hash { st = st.st } in
  (* Fails in 8.18 *)
  (* assert (not (Int.equal h1 h3)); *)
  (* Fails in 8.17 *)
  (* assert (Int.equal h1 h3); *)
  let* st = r ~st ~tac:"-" in
  let* st = r ~st ~tac:"now simpl; rewrite IHl." in
  let* st = r ~st ~tac:"Qed." in
  (* Search test, the inductive generates 6 entries *)
  let* st = r ~st ~tac:"Search naat." in
  check_search st 6;
  (* No goals after qed *)
  S.goals { st = extract_st st }

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
