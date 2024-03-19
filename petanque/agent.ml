(* Petanque *)

module State = struct
  type t = Coq.State.t

  let hash = Coq.State.hash
  let equal = Coq.State.equal

  let goals st =
    Coq.State.lemmas ~st
    |> Option.map (fun pf ->
           let pf = Coq.State.Proof.to_coq pf in
           let pf = Vernacstate.LemmaStack.get_top pf in
           let { Proof.goals; _ } = Declare.Proof.get pf |> Proof.data in
           Format.asprintf "goals: %d" (List.length goals))
end

module Start_error = struct
  type t = string
end

let init_coq ~debug =
  let load_module = Dynlink.loadfile in
  let load_plugin = Coq.Loader.plugin_handler None in
  Coq.Init.(coq_init { debug; load_module; load_plugin })

let cmdline : Coq.Workspace.CmdLine.t =
  { coqlib = Coq_config.coqlib
  ; coqcorelib = Filename.concat Coq_config.coqlib "../coq-core"
  ; ocamlpath = None
  ; vo_load_path = []
  ; ml_include_path = []
  ; args = []
  ; require_libraries = []
  }

let io =
  let trace hdr ?extra:_ msg =
    Format.eprintf "@[[trace] %s | %s @]@\n%!" hdr msg
  in
  let message ~lvl:_ ~message =
    Format.eprintf "@[[message] %s @]@\n%!" message
  in
  let diagnostics ~uri:_ ~version:_ _diags = () in
  let fileProgress ~uri:_ ~version:_ _pinfo = () in
  { Fleche.Io.CallBack.trace; message; diagnostics; fileProgress }

let init_fleche ~debug =
  let init = init_coq ~debug in
  Fleche.Io.CallBack.set io;
  let workspace = Coq.Workspace.default ~debug ~cmdline in
  Fleche.Doc.Env.make ~init ~workspace

let read_raw ~uri =
  let file = Lang.LUri.File.to_string_file uri in
  Stdlib.In_channel.(with_open_text file input_all)

let find_thm ~(doc : Fleche.Doc.t) ~thm =
  let { Fleche.Doc.toc; _ } = doc in
  match CString.Map.find_opt thm toc with
  | None ->
    Format.eprintf "@[[find_thm] Theorem not found!@\n@]%!";
    None
  | Some range ->
    Format.eprintf "@[[find_thm] Theorem found!@\n@]%!";
    (* let point = (range.start.line, range.start.character) in *)
    let point = (range.end_.line, range.end_.character) in
    let approx = Fleche.Info.PrevIfEmpty in
    let node = Fleche.Info.LC.node ~doc ~point approx in
    Option.map Fleche.Doc.Node.state node

let pp_diag fmt { Lang.Diagnostic.message; _ } =
  Format.fprintf fmt "%a" Pp.pp_with message

let print_diags (doc : Fleche.Doc.t) =
  let d = Fleche.Doc.diags doc in
  Format.(eprintf "@[<v>%a@]" (pp_print_list pp_diag) d)

let start ~uri ~thm =
  let debug = true in
  let env = init_fleche ~debug in
  let raw = read_raw ~uri in
  (* Format.eprintf "raw: @[%s@]%!" raw; *)
  let doc = Fleche.Doc.create ~env ~uri ~version:0 ~raw in
  print_diags doc;
  let target = Fleche.Doc.Target.End in
  let doc = Fleche.Doc.check ~io ~target ~doc () in
  find_thm ~doc ~thm

module Run_error = struct
  type t = string
end

let parse ~loc tac st =
  let str = Gramlib.Stream.of_string tac in
  let str = Coq.Parsing.Parsable.make ?loc str in
  Coq.Parsing.parse ~st str

let parse_and_execute_in ~loc tac st =
  let open Coq.Protect.E.O in
  let* ast = parse ~loc tac st in
  match ast with
  | Some ast -> (Fleche.Memo.Interp.eval (st, ast)).res
  (* On EOF we return the previous state, the command was the empty string or a
     comment *)
  | None -> Coq.Protect.E.ok st

let protect_to_option (r : _ Coq.Protect.E.t) : _ option =
  match r with
  | { r = Interrupted; feedback = _ } -> None
  | { r = Completed r; feedback = _ } -> Result.to_option r

let run_tac ~st ~tac =
  (* Improve with thm? *)
  let loc = None in
  Coq.State.in_stateM ~st ~f:(parse_and_execute_in ~loc tac) st
  |> protect_to_option
