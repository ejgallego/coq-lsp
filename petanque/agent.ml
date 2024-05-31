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

  (* JSON-RPC server reserved codes *)
  let to_code = function
    | Interrupted -> -32001
    | Parsing _ -> -32002
    | Coq _ -> -32003
    | Anomaly _ -> -32004
    | Theorem_not_found _ -> -32005
end

module R = struct
  type 'a t = ('a, Error.t) Result.t
end

module Run_result = struct
  type 'a t =
    | Proof_finished of 'a
    | Current_state of 'a
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
  let serverVersion _ = () in
  let serverStatus _ = () in
  { Fleche.Io.CallBack.trace
  ; message
  ; diagnostics
  ; fileProgress
  ; perfData
  ; serverVersion
  ; serverStatus
  }

let read_raw ~uri =
  let file = Lang.LUri.File.to_string_file uri in
  try Ok Coq.Compat.Ocaml_414.In_channel.(with_open_text file input_all)
  with Sys_error err -> Error err

let find_thm ~(doc : Fleche.Doc.t) ~thm =
  let { Fleche.Doc.toc; _ } = doc in
  match CString.Map.find_opt thm toc with
  | None ->
    let msg = Format.asprintf "@[[find_thm] Theorem not found!@]" in
    Error (Error.Theorem_not_found msg)
  | Some node ->
    if pet_debug then Format.eprintf "@[[find_thm] Theorem found!@\n@]%!";
    (* let point = (range.start.line, range.start.character) in *)
    Ok (Fleche.Doc.Node.state node)

let pp_diag fmt { Lang.Diagnostic.message; _ } =
  Format.fprintf fmt "%a" Pp.pp_with message

let print_diags (doc : Fleche.Doc.t) =
  let d = Fleche.Doc.diags doc in
  Format.(eprintf "@[<v>%a@]" (pp_print_list pp_diag) d)

let init ~token ~debug ~root =
  let init = init_coq ~debug in
  Fleche.Io.CallBack.set io;
  let dir = Lang.LUri.File.to_string_file root in
  (let open Coq.Compat.Result.O in
   let+ workspace = Coq.Workspace.guess ~token ~debug ~cmdline ~dir in
   let files = Coq.Files.make () in
   Fleche.Doc.Env.make ~init ~workspace ~files)
  |> Result.map_error (fun msg -> Error.Coq msg)

let start ~token ~env ~uri ~thm =
  match read_raw ~uri with
  | Ok raw ->
    (* Format.eprintf "raw: @[%s@]%!" raw; *)
    let doc = Fleche.Doc.create ~token ~env ~uri ~version:0 ~raw in
    print_diags doc;
    let target = Fleche.Doc.Target.End in
    let doc = Fleche.Doc.check ~io ~token ~target ~doc () in
    find_thm ~doc ~thm
  | Error err ->
    let msg = Format.asprintf "@[[read_raw] File not found %s@]" err in
    Error (Error.Theorem_not_found msg)

let parse ~loc tac st =
  let str = Gramlib.Stream.of_string tac in
  let str = Coq.Parsing.Parsable.make ?loc str in
  Coq.Parsing.parse ~st str

let proof_finished { Coq.Goals.goals; stack; shelf; given_up; _ } =
  List.for_all CList.is_empty [ goals; shelf; given_up ] && CList.is_empty stack

let parse_and_execute_in ~token ~loc tac st =
  let open Coq.Protect.E.O in
  let* ast = parse ~token ~loc tac st in
  match ast with
  | Some ast -> (
    let open Coq.Protect.E.O in
    let* st = Fleche.Memo.Interp.eval ~token (st, ast) in
    let+ goals = Fleche.Info.Goals.goals ~token ~st in
    match goals with
    | None -> Run_result.Proof_finished st
    | Some goals when proof_finished goals -> Run_result.Proof_finished st
    | _ -> Run_result.Current_state st)
  | None -> Coq.Protect.E.ok (Run_result.Current_state st)

let protect_to_result (r : _ Coq.Protect.E.t) : (_, _) Result.t =
  match r with
  | { r = Interrupted; feedback = _ } -> Error Error.Interrupted
  | { r = Completed (Error (User (_loc, msg))); feedback = _ } ->
    Error (Error.Coq (Pp.string_of_ppcmds msg))
  | { r = Completed (Error (Anomaly (_loc, msg))); feedback = _ } ->
    Error (Error.Anomaly (Pp.string_of_ppcmds msg))
  | { r = Completed (Ok r); feedback = _ } -> Ok r

let run_tac ~token ~st ~tac : (_ Run_result.t, Error.t) Result.t =
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

module Premise = struct
  type t =
    { full_name : string
          (* should be a Coq DirPath, but let's go step by step *)
    ; file : string (* file (in FS format) where the premise is found *)
    ; kind : (string, string) Result.t (* type of object *)
    ; range : (Lang.Range.t, string) Result.t (* a range if known *)
    ; offset : (int * int, string) Result.t
          (* a offset in the file if known (from .glob files) *)
    ; raw_text : (string, string) Result.t (* raw text of the premise *)
    }
end

(* We need some caching here otherwise it is very expensive to re-parse the glob
   files all the time.

   XXX move this caching to Flèche. *)
module Memo = struct
  module H = Hashtbl.Make (CString)

  let table_glob = H.create 1000

  let open_file glob =
    match H.find_opt table_glob glob with
    | Some g -> g
    | None ->
      let g = Coq.Glob.open_file glob in
      H.add table_glob glob g;
      g

  let table_source = H.create 1000

  let input_source file =
    match H.find_opt table_source file with
    | Some res -> res
    | None ->
      if Sys.file_exists file then (
        let res =
          Ok Coq.Compat.Ocaml_414.In_channel.(with_open_text file input_all)
        in
        H.add table_source file res;
        res)
      else
        let res = Error "source file is not available" in
        H.add table_source file res;
        res
end

let info_of ~glob ~name =
  let open Coq.Compat.Result.O in
  let* g = Memo.open_file glob in
  let+ { Coq.Glob.Info.kind; offset } = Coq.Glob.get_info g name in
  (kind, offset)

let raw_of ~file ~offset =
  match offset with
  | Ok (bp, ep) ->
    let open Coq.Compat.Result.O in
    let* c = Memo.input_source file in
    if String.length c < ep then Error "offset out of bounds"
    else Ok (String.sub c bp (ep - bp + 1))
  | Error err -> Error ("offset information is not available: " ^ err)

let to_premise (p : Coq.Library_file.Entry.t) : Premise.t =
  let { Coq.Library_file.Entry.name; typ = _; file } = p in
  let file = Filename.(remove_extension file ^ ".v") in
  let glob = Filename.(remove_extension file ^ ".glob") in
  let range = Error "not implemented yet" in
  let kind, offset = info_of ~glob ~name |> Coq.Compat.Result.split in
  let raw_text = raw_of ~file ~offset in
  { full_name = name; file; kind; range; offset; raw_text }

let premises ~token ~st =
  (let open Coq.Protect.E.O in
   let* all_libs = Coq.Library_file.loaded ~token ~st in
   let+ all_premises = Coq.Library_file.toc ~token ~st all_libs in
   List.map to_premise all_premises)
  |> protect_to_result
