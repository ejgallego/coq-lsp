(************************************************************************)
(* Flèche Document Manager                                              *)
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Copyright 2019-2022 Inria           -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(* open Lsp_util
 * module LSP = Lsp.Base *)

(* [node list] is a very crude form of a meta-data map "loc -> data" , where for
   now [data] is only the goals. *)
type node =
  { ast : Lang.Ast.t  (** Ast of node *)
  ; state : Lang.State.t  (** (Full) State of node *)
  ; memo_info : string
  }

(* Private. A doc is a list of nodes for now. The first element in the list is
   assumed to be the tip of the document. The initial document is the empty
   list. *)
type t =
  { uri : string
  ; version : int
  ; contents : string
  ; root : Lang.State.t
  ; nodes : node list
  }

(* let mk_error ~doc pos msg =
 *   LSP.mk_diagnostics ~uri:doc.uri ~version:doc.version [pos, 1, msg, None] *)

let mk_doc state =
  let root_state, vo_load_path, ml_load_path, _ = state in
  let requires = [ ("Coq.Init.Prelude", None, Some (Lib.Import, None)) ] in
  let env = { Lang.Init.Doc.vo_load_path; ml_load_path; requires } in
  let name = Names.(DirPath.make [ Id.of_string "foo" ]) in
  Lang.Init.Doc.make ~root_state ~env ~name

let create ~state ~uri ~version ~contents =
  { uri; contents; version; root = mk_doc state; nodes = [] }

(* XXX: Save on close? *)
(* let close_doc _modname = () *)

let parse_stm ~st ps =
  let mode = Lang.State.mode ~st in
  let st = Lang.State.parsing ~st in
  let parse ps =
    (* Coq is missing this, so we add it here. Note that this MUST run inside
       coq_protect *)
    Control.check_for_interrupt ();
    Lang.Parse.(parse st mode) ps
  in
  Stats.record ~kind:Stats.Kind.Parsing ~f:(Lang.Protect.eval ~f:parse) ps

(* Gross hack *)
let proof_st = ref None

let register_hack_proof_recover ast st =
  match Lang.Ast.View.kind ast with
  | Open () ->
    proof_st := Some st;
    ()
  | _ -> ()

(* Simple heuristic for Qed. *)
let state_recovery_heuristic st ast =
  match Lang.Ast.View.kind ast with
  (* Drop the top proof state if we reach a faulty Qed. *)
  | End () ->
    let st = Option.default st !proof_st in
    Io.Log.error "recovery" (Memo.input_info (ast, st));
    proof_st := None;
    Lang.State.drop_proofs ~st
  | _ -> st

type process_action =
  | EOF
  | Skip
  | Process of Lang.Ast.t

(* Make each fb a diag *)
let _pp_located fmt (_loc, pp) = Pp.pp_with fmt pp

let pp_words fmt w =
  if w < 1024.0 then Format.fprintf fmt "%.0f  w" w
  else if w < 1024.0 *. 1024.0 then Format.fprintf fmt "%.2f Kw" (w /. 1024.0)
  else Format.fprintf fmt "%.2f Mw" (w /. (1024.0 *. 1024.0))

let mk_diag ?(extra = []) range severity message =
  let range = Lang.Loc.to_range range in
  let message = Lang.Pp.to_string message in
  Types.Diagnostic.{ range; severity; message; extra }

(* modular error diagnostic generation *)
let mk_error_diagnostic ~loc ~msg ~ast =
  match Lang.Ast.View.kind ast with
  | Require { prefix; refs } ->
    let extra = [ Types.Diagnostic.Extra.FailedRequire { prefix; refs } ] in
    mk_diag ~extra loc 1 msg
  | _ -> mk_diag loc 1 msg

let feed_to_diag ~loc (range, severity, message) =
  let range = Option.default loc range in
  mk_diag range severity message

let send_processing_diag ~uri ~version loc diags =
  let proc_diag = mk_diag loc 3 (Lang.Pp.str "Processing") in
  Io.Report.diagnostics ~uri ~version (proc_diag :: diags)

let print_parsing_debug_info loc ast =
  let line = (Lang.Loc.to_range loc).start.line in
  let line = "[l: " ^ string_of_int line ^ "] " in
  Io.Log.error "coq"
    ("parsed sentence: " ^ line ^ Lang.Pp.to_string (Lang.Ast.print ast))

let process_feedback ~loc fbs = List.map (feed_to_diag ~loc) fbs

let interp_and_info ~parsing_time ~st ~fb_queue ast =
  let { Gc.major_words = mw_prev; _ } = Gc.quick_stat () in
  let { Memo.Stats.res; cache_hit; memory = _; time } =
    Memo.interp_command ~st ~fb_queue ast
  in
  let cptime = Stats.get ~kind:Stats.Kind.Parsing in
  let cetime = Stats.get ~kind:Stats.Kind.Exec in
  let { Gc.major_words = mw_after; _ } = Gc.quick_stat () in
  let memo_info =
    Format.asprintf
      "Cache Hit: %b | Parse (s/c): %.4f / %.2f | Exec (s/c): %.4f / %.2f"
      cache_hit parsing_time cptime time cetime
  in
  let mem_info =
    Format.asprintf "major words: %a | diff %a" pp_words mw_after pp_words
      (mw_after -. mw_prev)
  in
  (res, memo_info ^ "\n" ^ mem_info)

(* XXX: Imperative problem *)
let process_and_parse ~uri ~version ~fb_queue doc =
  let loc = Lang.Loc.initial ~uri in
  let doc_handle =
    Lang.Parse.Parsable.make ~loc Gramlib.Stream.(of_string doc.contents)
  in
  let rec stm doc st diags =
    if Debug.parsing then Io.Log.error "coq" "parsing sentence";
    (* Parsing *)
    let action, diags, parsing_time =
      match parse_stm ~st doc_handle with
      | Lang.Protect.R.Interrupted, time -> (EOF, diags, time)
      | Lang.Protect.R.Completed res, time -> (
        match res with
        | Ok None -> (EOF, diags, time)
        | Ok (Some ast) -> (Process ast, diags, time)
        | Error (loc, msg) ->
          let loc = Option.get loc in
          let diags = mk_diag loc 1 msg :: diags in
          Lang.Parse.discard_to_dot doc_handle;
          (Skip, diags, time))
    in
    (* Execution *)
    match action with
    (* End of file *)
    | EOF -> (doc, st, diags)
    | Skip -> stm doc st diags
    (* We interpret the command now *)
    | Process ast -> (
      let loc = Lang.Ast.loc ast |> Option.get in
      (* XXX Eager update! *)
      if Config.eager_diagnostics then
        send_processing_diag ~uri ~version loc diags;
      if Debug.parsing then print_parsing_debug_info loc ast;
      register_hack_proof_recover ast st;
      let res, memo_info = interp_and_info ~parsing_time ~st ~fb_queue ast in
      match res with
      | Lang.Protect.R.Interrupted ->
        (* Exit *)
        (doc, st, diags)
      | Lang.Protect.R.Completed res -> (
        match res with
        | Ok { res = state; feedback } ->
          (* let goals = Lang.State.goals *)
          let ok_diag = mk_diag loc 3 (Lang.Pp.str "OK") in
          let diags = if Config.ok_diag then ok_diag :: diags else diags in
          let fb_diags = process_feedback ~loc feedback in
          let diags = fb_diags @ diags in
          let node = { ast; state; memo_info } in
          let doc = { doc with nodes = node :: doc.nodes } in
          stm doc state diags
        | Error (err_loc, msg) ->
          let loc = Option.default loc err_loc in
          let diags = mk_error_diagnostic ~loc ~msg ~ast :: diags in
          (* FB should be handled by Coq.Protect.eval XXX *)
          let fb_diags = List.rev !fb_queue |> process_feedback ~loc in
          fb_queue := [];
          let diags = fb_diags @ diags in
          let st = state_recovery_heuristic st ast in
          let node = { ast; state = st; memo_info } in
          let doc = { doc with nodes = node :: doc.nodes } in
          stm doc st diags))
  in
  (* we re-start from the root *)
  stm doc doc.root []

let print_stats () =
  (if Config.mem_stats then
   let size = Memo.mem_stats () in
   Io.Log.error "stats" (string_of_int size));

  Io.Log.error "cache" (Stats.dump ());
  Io.Log.error "cache" (Memo.CacheStats.stats ());
  Io.Log.error "coq parsing" (Cstats.dump ());
  Cstats.reset ();
  Memo.CacheStats.reset ();
  Stats.reset ()

let gen l = String.make (String.length l) ' '

let rec md_map_lines coq l =
  match l with
  | [] -> []
  | l :: ls ->
    if String.equal "```" l then gen l :: md_map_lines (not coq) ls
    else (if coq then l else gen l) :: md_map_lines coq ls

let markdown_process text =
  let lines = String.split_on_char '\n' text in
  let lines = md_map_lines false lines in
  String.concat "\n" lines

let process_contents ~uri ~contents =
  let ext = Filename.extension uri in
  let is_markdown = String.equal ext ".mv" in
  if is_markdown then markdown_process contents else contents

let check ~ofmt:_ ~doc ~fb_queue =
  let uri, version, contents = (doc.uri, doc.version, doc.contents) in
  let processed_content = process_contents ~uri ~contents in
  (* Start library *)
  let doc = { doc with nodes = []; contents = processed_content } in
  let doc, st, diags = (process_and_parse ~uri ~version ~fb_queue) doc in
  let doc = { doc with nodes = List.rev doc.nodes; contents } in
  print_stats ();
  (* (doc, st, json_of_diags ~uri ~version diags) *)
  (doc, st, diags)
