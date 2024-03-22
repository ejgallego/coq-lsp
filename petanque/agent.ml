(* Petanque *)

let pet_debug = false

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
    let msg = Format.asprintf "@[[find_thm] Theorem not found!@]" in
    Error msg
  | Some range ->
    if pet_debug then Format.eprintf "@[[find_thm] Theorem found!@\n@]%!";
    (* let point = (range.start.line, range.start.character) in *)
    let point = (range.end_.line, range.end_.character) in
    let approx = Fleche.Info.PrevIfEmpty in
    let node = Fleche.Info.LC.node ~doc ~point approx in
    let error =
      Format.asprintf "@[[find_thm] No node found for point (%d, %d) @]"
        (fst point) (snd point)
    in
    Base.Result.of_option ~error node |> Result.map Fleche.Doc.Node.state

let pp_diag fmt { Lang.Diagnostic.message; _ } =
  Format.fprintf fmt "%a" Pp.pp_with message

let print_diags (doc : Fleche.Doc.t) =
  let d = Fleche.Doc.diags doc in
  Format.(eprintf "@[<v>%a@]" (pp_print_list pp_diag) d)

let start ~uri ~thm =
  let debug = false in
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

let protect_to_result (r : _ Coq.Protect.E.t) : (_, _) Result.t =
  match r with
  | { r = Interrupted; feedback = _ } -> Error "operation interrupted"
  | { r = Completed (Error _); feedback = _ } -> Error "operation errored"
  | { r = Completed (Ok r); feedback = _ } -> Ok r

let run_tac ~st ~tac : (Coq.State.t, Run_error.t) Result.t =
  (* Improve with thm? *)
  let loc = None in
  Coq.State.in_stateM ~st ~f:(parse_and_execute_in ~loc tac) st
  |> protect_to_result
