open Petanque_json

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

let extract_st (st : Protocol.RunTac.Response.t) =
  match st with
  | Proof_finished st | Current_state st -> st

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
    let st = extract_st st in
    S.run_tac { st; tac }
  in
  (* Will this work on Windows? *)
  let root, uri = prepare_paths () in
  let* _env = S.set_workspace { debug; root } in
  let* st = S.start { uri; pre_commands = None; thm = "rev_snoc_cons" } in
  let* premises = S.premises { st } in
  (if print_premises then
     Format.(eprintf "@[%a@]@\n%!" (pp_print_list pp_premise) premises));
  let* st = S.run_tac { st; tac = "induction l." } in
  let* st = r ~st ~tac:"-" in
  let* st = r ~st ~tac:"reflexivity." in
  let* st = r ~st ~tac:"-" in
  let* st = r ~st ~tac:"now simpl; rewrite IHl." in
  let* st = r ~st ~tac:"Qed." in
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
