open Fleche

let message ~io =
  let lvl = Io.Level.Info in
  Format.kasprintf (fun message ->
      Io.Report.msg ~io ~lvl "[baseline] %s" message)

(* Log with newline *)
let log ~io:_ =
  Stdlib.Format.eprintf "[baseline] ";
  Stdlib.Format.(
    kfprintf
      (fun fmt ->
        pp_print_newline fmt ();
        pp_print_flush fmt ())
      err_formatter)

(* Log without newline *)
let log_line ~io:_ =
  let reset = Spectrum.prepare_ppf Stdlib.Format.err_formatter in
  Stdlib.Format.eprintf
    "\r                                                                                       ";
  Stdlib.Format.eprintf "\r[baseline] ";
  Stdlib.Format.(
    kfprintf
      (fun fmt ->
        pp_print_flush fmt ();
        reset ())
      err_formatter)

let get_goals ~token ~st =
  match Info.Goals.goals ~token ~st with
  | { Coq.Protect.E.r = Interrupted; _ }
  | { r = Completed (Error _); _ }
  | { r = Completed (Ok None); _ } -> []
  | { r = Completed (Ok (Some goals)); _ } -> goals.goals

let get_goals_thm ~token { Common.ThmDecl.names = _; node } =
  let st = node.state in
  get_goals ~token ~st

module TacResult = struct
  type t =
    { names : string list
    ; goals : Pp.t Coq.Goals.Reified_goal.t list
    ; feedback : Loc.t Coq.Message.t list
    }

  (* let pp fmt { names; goals; feedback } = () *)
end

let run_tac_silent = true

let redirect_write fdesc f =
  (* Should call fflush on fdesc, where is the ocaml api? *)
  let bak = Unix.dup fdesc in
  let new_ = Unix.openfile "/dev/null" [ Unix.O_WRONLY ] 0o644 in
  Unix.dup2 new_ fdesc;
  Unix.close new_;
  let finally () =
    Unix.dup2 bak fdesc;
    Unix.close bak
  in
  Fun.protect ~finally f

(* We capture stderr/stdin as to have better output for hammer *)
let run_tac ~token ~st ~timeout tac =
  if run_tac_silent then
    redirect_write Unix.stdout (fun () ->
        redirect_write Unix.stderr (fun () ->
            Common.run_tac ~token ~st ~timeout tac))
  else Common.run_tac ~token ~st ~timeout tac

(* Dont' forget the dot at the end of [tac] *)
let apply_tac ~token ~tac { Common.ThmDecl.names; node } =
  let derror = Lang.Diagnostic.Severity.error in
  let st = node.state in
  (* Timeout from env or default 5.0 *)
  let timeout =
    match Sys.getenv_opt "BASE_TIMEOUT" with
    | Some t -> float_of_string t
    | None -> 5.0
  in
  let st, feedback =
    match run_tac ~token ~st ~timeout tac with
    | Coq.Protect.E.{ r = Interrupted; feedback } ->
      (* This can happen in timeouts, etc... *)
      let msg = Pp.(str "Coq was interrupted while executing the tactic") in
      let msg = { Coq.Message.Payload.range = None; msg; quickFix = None} in
      (st, (derror, msg) :: feedback)
    | Coq.Protect.E.{ r = Completed (Error (User { range; msg; _ })); feedback }
    | Coq.Protect.E.{ r = Completed (Error (Anomaly { range; msg; _})); feedback } ->
      let msg = { Coq.Message.Payload.range; msg; quickFix = None} in
      (st, (derror, msg) :: feedback)
    | Coq.Protect.E.{ r = Completed (Ok None); feedback } ->
      let msg = Pp.(str "EOF when parsing tactic") in
      let msg = { Coq.Message.Payload.range = None; msg ; quickFix = None} in
      (st, (derror, msg) :: feedback)
    | Coq.Protect.E.{ r = Completed (Ok (Some st)); feedback } -> (st, feedback)
  in
  let goals = get_goals ~token ~st in
  { TacResult.names; goals; feedback }

let check_proved goals =
  List.filter_map
    (fun { TacResult.names; goals; feedback = _ } ->
      if CList.is_empty goals then Some names else None)
    goals

let pp_names fmt names = Format.fprintf fmt "{%s}" (String.concat " " names)

let traced ~io ~doc_name ~tac ~total f idx x =
  let ({ TacResult.names; goals; _ } as res) = f x in
  log_line ~io "%s | [%s] (%d/%d) %a open_goals :%d" doc_name tac idx total
    pp_names names (List.length goals);
  res

(* Display list of proven theorems *)
let display_theorems = false

let check_tac ~io ~token ~thms ~doc_name ~tac =
  let pp_sep = Format.pp_print_space in
  let total = List.length thms in
  let goals_after =
    List.mapi (traced ~io ~doc_name ~tac ~total (apply_tac ~token ~tac)) thms
  in
  let proved_thms = check_proved goals_after in
  let proved_thms_to_show = if display_theorems then proved_thms else [] in
  log_line ~io "%s | [%s] theorems proved (%d/%d):@\n @[<hov>%a@]" doc_name tac
    (List.length proved_thms) total
    Format.(pp_print_list ~pp_sep pp_names)
    proved_thms_to_show;
  proved_thms

module BaselineResult = struct
  type t =
    { tactic : string
    ; proved : string list
    }
  [@@deriving yojson]
end

let do_baseline ~io ~token ~doc =
  let thms = Common.get_theorems ~doc in
  let goals_original = List.map (get_goals_thm ~token) thms in
  let doc_name =
    Stdlib.Filename.basename (Lang.LUri.File.to_string_file doc.uri)
  in
  let check = check_tac ~io ~token ~thms ~doc_name in
  (* EJGA: Note OCaml will start evaluating this by the last element, so I've
     reversed them. *)
  let proved_baselines =
    [ ("tactician-base", check ~tac:"by synth.")
    ; ("hammer", check ~tac:"by hammer.")
    ; ("sauto", check ~tac:"by sauto.")
    ; ("auto", check ~tac:"by auto.")
    ]
  in
  message ~io "number of theorems %d" (List.length thms);
  message ~io "number of goals %d" List.(length (concat goals_original));
  message ~io "baseline report end -------------------------";
  (* If timeout is given add it to the name *)
  let timeout =
    match Sys.getenv_opt "BASE_TIMEOUT" with
    | Some t -> "_" ^ t
    | None -> ""
  in
  let fn = Lang.LUri.File.to_string_file doc.uri ^ timeout ^ ".baseline.json" in

  let summary =
    List.map
      (fun (tactic, proved) ->
        BaselineResult.{ tactic; proved = List.flatten proved })
      proved_baselines
  in

  let oc = open_out fn in
  output_string oc
  @@ (`List (List.map BaselineResult.to_yojson summary) |> Yojson.Safe.to_string)
  ^ "\n";
  close_out oc;
  ()

let do_require_tauto ~io:_ =
  let from, library = (Some "Hammer", "Tactics") in
  let tactics =
    Coq.Workspace.Require.{ library; from; flags = Some (Import, None) }
  in
  (* From Hammer Require Import Hammer *)
  let from, library = (Some "Hammer", "Hammer") in
  let hammer =
    Coq.Workspace.Require.{ library; from; flags = Some (Import, None) }
  in
  let from, library = (Some "Tactician", "Ltac1") in
  let tactician =
    Coq.Workspace.Require.{ library; from; flags = Some (Import, None) }
  in
  ignore([ tactics; hammer; tactician ]);
  [ ]

let do_baseline ~io ~token ~(doc : Fleche.Doc.t) =
  match Common.completed_without_error ~doc with
  | None -> do_baseline ~io ~token ~doc
  | Some diags ->
    let file = Lang.LUri.File.to_string_file doc.uri in
    log ~io "@[Document creation for file %s did fail!!@\nDiags:@\n @[%a@]" file
      Common.pp_diags diags

let () =
  Theory.Register.InjectRequire.add do_require_tauto;
  Theory.Register.Completed.add do_baseline
