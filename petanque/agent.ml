(************************************************************************)
(* Flèche => RL agent: petanque                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)

let pet_debug = false

module State = struct
  type t = Coq.State.t

  let hash = Coq.State.hash
  let equal = Coq.State.equal
end

module Env = struct
  type t = Fleche.Doc.Env.t
end

(** Petanque errors *)
module Error = struct
  type t =
    | Interrupted
    | Parsing of string
    | Coq of string
    | Anomaly of string
    | Theorem_not_found of string

  let to_string = function
    | Interrupted -> Format.asprintf "Interrupted"
    | Parsing msg -> Format.asprintf "Parsing: %s" msg
    | Coq msg -> Format.asprintf "Coq: %s" msg
    | Anomaly msg -> Format.asprintf "Anomaly: %s" msg
    | Theorem_not_found msg -> Format.asprintf "Theorem_not_found: %s" msg
end

module R = struct
  type 'a t = ('a, Error.t) Result.t
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

let trace_stderr hdr ?extra:_ msg =
  Format.eprintf "@[[trace] %s | %s @]@\n%!" hdr msg

let trace_ref = ref trace_stderr

let message_stderr ~lvl:_ ~message =
  Format.eprintf "@[[message] %s @]@\n%!" message

let message_ref = ref message_stderr

let io =
  let trace hdr ?extra msg = !trace_ref hdr ?extra msg in
  let message ~lvl ~message = !message_ref ~lvl ~message in
  let diagnostics ~uri:_ ~version:_ _diags = () in
  let fileProgress ~uri:_ ~version:_ _pinfo = () in
  let perfData ~uri:_ ~version:_ _perf = () in
  { Fleche.Io.CallBack.trace; message; diagnostics; fileProgress; perfData }

let read_raw ~uri =
  let file = Lang.LUri.File.to_string_file uri in
  Fleche.Compat.Ocaml_414.In_channel.(with_open_text file input_all)

let find_thm ~(doc : Fleche.Doc.t) ~thm =
  let { Fleche.Doc.toc; _ } = doc in
  match CString.Map.find_opt thm toc with
  | None ->
    let msg = Format.asprintf "@[[find_thm] Theorem not found!@]" in
    Error (Error.Theorem_not_found msg)
  | Some range ->
    if pet_debug then Format.eprintf "@[[find_thm] Theorem found!@\n@]%!";
    (* let point = (range.start.line, range.start.character) in *)
    let point = (range.end_.line, range.end_.character) in
    let approx = Fleche.Info.PrevIfEmpty in
    let node = Fleche.Info.LC.node ~doc ~point approx in
    let error =
      Error.Theorem_not_found
        (Format.asprintf "@[[find_thm] No node found for point (%d, %d) @]"
           (fst point) (snd point))
    in
    Base.Result.of_option ~error node |> Result.map Fleche.Doc.Node.state

let pp_diag fmt { Lang.Diagnostic.message; _ } =
  Format.fprintf fmt "%a" Pp.pp_with message

let print_diags (doc : Fleche.Doc.t) =
  let d = Fleche.Doc.diags doc in
  Format.(eprintf "@[<v>%a@]" (pp_print_list pp_diag) d)

let init ~token ~debug ~root =
  let init = init_coq ~debug in
  Fleche.Io.CallBack.set io;
  let dir = Lang.LUri.File.to_string_file root in
  (let open Fleche.Compat.Result.O in
   let+ workspace = Coq.Workspace.guess ~token ~debug ~cmdline ~dir in
   let files = Coq.Files.make () in
   Fleche.Doc.Env.make ~init ~workspace ~files)
  |> Result.map_error (fun msg -> Error.Coq msg)

let start ~token ~env ~uri ~thm =
  let raw = read_raw ~uri in
  (* Format.eprintf "raw: @[%s@]%!" raw; *)
  let doc = Fleche.Doc.create ~token ~env ~uri ~version:0 ~raw in
  print_diags doc;
  let target = Fleche.Doc.Target.End in
  let doc = Fleche.Doc.check ~io ~token ~target ~doc () in
  find_thm ~doc ~thm

let parse ~loc tac st =
  let str = Gramlib.Stream.of_string tac in
  let str = Coq.Parsing.Parsable.make ?loc str in
  Coq.Parsing.parse ~st str

let parse_and_execute_in ~token ~loc tac st =
  let open Coq.Protect.E.O in
  let* ast = parse ~token ~loc tac st in
  match ast with
  | Some ast -> Fleche.Memo.Interp.eval ~token (st, ast)
  (* On EOF we return the previous state, the command was the empty string or a
     comment *)
  | None -> Coq.Protect.E.ok st

let protect_to_result (r : _ Coq.Protect.E.t) : (_, _) Result.t =
  match r with
  | { r = Interrupted; feedback = _ } -> Error Error.Interrupted
  | { r = Completed (Error (User (_loc, msg))); feedback = _ } ->
    Error (Error.Coq (Pp.string_of_ppcmds msg))
  | { r = Completed (Error (Anomaly (_loc, msg))); feedback = _ } ->
    Error (Error.Anomaly (Pp.string_of_ppcmds msg))
  | { r = Completed (Ok r); feedback = _ } -> Ok r

let run_tac ~token ~st ~tac : (Coq.State.t, Error.t) Result.t =
  (* Improve with thm? *)
  let loc = None in
  Coq.State.in_stateM ~token ~st ~f:(parse_and_execute_in ~token ~loc tac) st
  |> protect_to_result

let goals ~token ~st =
  let f goals =
    let f = Coq.Goals.map_reified_goal ~f:Pp.string_of_ppcmds in
    let g = Pp.string_of_ppcmds in
    Option.map (Coq.Goals.map_goals ~f ~g) goals
  in
  Coq.Protect.E.map ~f (Fleche.Info.Goals.goals ~token ~st) |> protect_to_result

let premises ~token ~st =
  (let open Coq.Protect.E.O in
   let* all_libs = Coq.Library_file.loaded ~token ~st in
   let+ all_premises = Coq.Library_file.toc ~token ~st all_libs in
   List.map fst all_premises)
  |> protect_to_result
