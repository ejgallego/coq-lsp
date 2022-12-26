(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2022 Inria           -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

(* open Lsp_util
 * module LSP = Lsp.Base *)

let hd_opt ~default l =
  match l with
  | [] -> default
  | h :: _ -> h

(* [node list] is a very crude form of a meta-data map "loc -> data" , where for
   now [data] is only the goals. *)
type node =
  { loc : Loc.t
  ; ast : Coq.Ast.t option  (** Ast of node *)
  ; state : Coq.State.t  (** (Full) State of node *)
  ; diags : Types.Diagnostic.t list
  ; memo_info : string
  }

module Completion = struct
  type t =
    | Yes
    | Stopped of Loc.t (* Location of the last valid token *)
end

(* Private. A doc is a list of nodes for now. The first element in the list is
   assumed to be the tip of the document. The initial document is the empty
   list. *)
type t =
  { uri : string
  ; version : int
  ; contents : string
  ; root : Coq.State.t
  ; nodes : node list
  ; diags_dirty : bool  (** Used to optimize `eager_diagnostics` *)
  ; completed : Completion.t
  }

let mk_doc root_state workspace =
  let libname = Names.(DirPath.make [ Id.of_string "foo" ]) in
  let require_libs = [ ("Coq.Init.Prelude", None, Some (Lib.Import, None)) ] in
  Coq.Init.doc_init ~root_state ~workspace ~libname ~require_libs

let init_loc ~uri = Loc.initial (InFile { dirpath = None; file = uri })

let create ~state ~workspace ~uri ~version ~contents =
  { uri
  ; contents
  ; version
  ; root = mk_doc state workspace
  ; nodes = []
  ; diags_dirty = false
  ; completed = Stopped (init_loc ~uri)
  }

let bump_version ~version ~text doc =
  (* We need to resume checking in full when a new document *)
  { doc with
    version
  ; nodes = []
  ; contents = text
  ; diags_dirty = false
  ; completed = Stopped (init_loc ~uri:doc.uri)
  }

let add_node ~node doc =
  let diags_dirty = if node.diags <> [] then true else doc.diags_dirty in
  { doc with nodes = node :: doc.nodes; diags_dirty }

let concat_diags doc = List.concat_map (fun node -> node.diags) doc.nodes

let send_eager_diagnostics ~uri ~version ~doc =
  (* this is too noisy *)
  (* let proc_diag = mk_diag loc 3 (Pp.str "Processing") in *)
  (* Io.Report.diagnostics ~uri ~version (proc_diag :: doc.diags)); *)
  if doc.diags_dirty && !Config.v.eager_diagnostics then (
    let diags = concat_diags doc in
    Io.Report.diagnostics ~uri ~version diags;
    { doc with diags_dirty = false })
  else doc

let set_completion ~completed doc = { doc with completed }

(* XXX: Save on close? *)
(* let close_doc _modname = () *)

let parse_stm ~st ps =
  let mode = Coq.State.mode ~st in
  let st = Coq.State.parsing ~st in
  let parse ps =
    (* Coq is missing this, so we add it here. Note that this MUST run inside
       coq_protect *)
    Control.check_for_interrupt ();
    Vernacstate.Parser.parse st Pvernac.(main_entry mode) ps
    |> Option.map Coq.Ast.of_coq
  in
  Stats.record ~kind:Stats.Kind.Parsing ~f:(Coq.Protect.eval ~f:parse) ps

(* Read the input stream until a dot or a "end of proof" token is encountered *)
let parse_to_terminator : unit Pcoq.Entry.t =
  (* type 'a parser_fun = { parser_fun : te LStream.t -> 'a } *)
  let rec dot st =
    match Gramlib.LStream.next st with
    | Tok.KEYWORD ("." | "..." | "Qed" | "Defined" | "Admitted") | Tok.BULLET _
      -> ()
    | Tok.EOI -> ()
    | _ -> dot st
  in
  Pcoq.Entry.of_parser "Coqtoplevel.dot" { parser_fun = dot }

(* If an error occurred while parsing, we try to read the input until a dot
   token is encountered. We assume that when a lexer error occurs, at least one
   char was eaten *)

let rec discard_to_dot ps =
  try Pcoq.Entry.parse parse_to_terminator ps with
  | CLexer.Error.E _ -> discard_to_dot ps
  | e when CErrors.noncritical e -> ()

(* Gross hack *)
let proof_st = ref None

let register_hack_proof_recover ast st =
  match (Coq.Ast.to_coq ast).CAst.v.Vernacexpr.expr with
  | Vernacexpr.VernacStartTheoremProof _ ->
    proof_st := Some st;
    ()
  | _ -> ()

(* Simple heuristic for Qed. *)
let state_recovery_heuristic st v =
  match (Coq.Ast.to_coq v).CAst.v.Vernacexpr.expr with
  (* Drop the top proof state if we reach a faulty Qed. *)
  | Vernacexpr.VernacEndProof _ ->
    let st = Option.default st !proof_st in
    Io.Log.error "recovery" (Memo.input_info (v, st));
    proof_st := None;
    Coq.State.drop_proofs ~st
  | _ -> st

let debug_parsed_sentence ~ast =
  let loc = Coq.Ast.loc ast |> Option.get in
  let line = "[l: " ^ string_of_int loc.Loc.line_nb ^ "] " in
  Io.Log.error "coq"
    ("parsed sentence: " ^ line ^ Pp.string_of_ppcmds (Coq.Ast.print ast))

type process_action =
  | EOF of Completion.t (* completed *)
  | Skip of Loc.t * Loc.t (* span of the skipped sentence + last valid token *)
  | Process of Coq.Ast.t (* ast to process *)

(* Make each fb a diag *)
let _pp_located fmt (_loc, pp) = Pp.pp_with fmt pp

let pp_words fmt w =
  if w < 1024.0 then Format.fprintf fmt "%.0f  w" w
  else if w < 1024.0 *. 1024.0 then Format.fprintf fmt "%.2f Kw" (w /. 1024.0)
  else Format.fprintf fmt "%.2f Mw" (w /. (1024.0 *. 1024.0))

let mk_diag ?(extra = []) range severity message =
  let range = Types.to_range range in
  let message = Pp.string_of_ppcmds message in
  Types.Diagnostic.{ range; severity; message; extra }

(* modular error diagnostic generation *)
let mk_error_diagnostic ~loc ~msg ~ast =
  match (Coq.Ast.to_coq ast).v with
  | Vernacexpr.{ expr = VernacRequire (prefix, _export, module_refs); _ } ->
    let refs = List.map fst module_refs in
    let extra = [ Types.Diagnostic.Extra.FailedRequire { prefix; refs } ] in
    mk_diag ~extra loc 1 msg
  | _ -> mk_diag loc 1 msg

let feed_to_diag ~loc (range, severity, message) =
  let range = Option.default loc range in
  mk_diag range severity message

let process_feedback ~loc fbs = List.map (feed_to_diag ~loc) fbs

let interp_and_info ~parsing_time ~st ~fb_queue ast =
  let { Gc.major_words = mw_prev; _ } = Gc.quick_stat () in
  (* memo memory stats are disabled: slow and misleading *)
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
  (res, memo_info ^ "\n___\n" ^ mem_info)

let build_span start_loc end_loc =
  Loc.
    { start_loc with
      line_nb_last = end_loc.line_nb_last
    ; bol_pos_last = end_loc.bol_pos_last
    ; ep = end_loc.ep
    }

(* XXX: Imperative problem *)
let process_and_parse ~uri ~version ~fb_queue doc last_tok doc_handle =
  let rec stm doc st last_tok =
    let doc = send_eager_diagnostics ~uri ~version ~doc in
    if Debug.parsing then Io.Log.error "coq" "parsing sentence";
    (* Parsing *)
    let action, parsing_diags, parsing_time =
      let start_loc = Pcoq.Parsable.loc doc_handle |> CLexer.after in
      match parse_stm ~st doc_handle with
      | Coq.Protect.R.Interrupted, time -> (EOF (Stopped last_tok), [], time)
      | Coq.Protect.R.Completed res, time -> (
        match res with
        | Ok None -> (EOF Yes, [], time)
        | Ok (Some ast) ->
          let () = if Debug.parsing then debug_parsed_sentence ~ast in
          (Process ast, [], time)
        | Error (loc, msg) ->
          let err_loc = Option.get loc in
          let diags = [ mk_diag err_loc 1 msg ] in
          discard_to_dot doc_handle;
          let last_tok = Pcoq.Parsable.loc doc_handle in
          let span_loc = build_span start_loc last_tok in
          (Skip (span_loc, last_tok), diags, time))
    in
    (* Execution *)
    match action with
    (* End of file *)
    | EOF completed -> set_completion ~completed doc
    | Skip (span_loc, last_tok) ->
      (* We add the parsing diags *)
      let node =
        { loc = span_loc
        ; ast = None
        ; diags = parsing_diags
        ; state = st
        ; memo_info = ""
        }
      in
      let doc = add_node ~node doc in
      stm doc st last_tok
    (* We interpret the command now *)
    | Process ast -> (
      let ast_loc = Coq.Ast.loc ast |> Option.get in
      (* We register pre-interp for now *)
      register_hack_proof_recover ast st;
      let res, memo_info = interp_and_info ~parsing_time ~st ~fb_queue ast in
      match res with
      | Coq.Protect.R.Interrupted ->
        (* Exit *)
        set_completion ~completed:(Stopped last_tok) doc
      | Coq.Protect.R.Completed res -> (
        (* We can resume checking from this point then *)
        let last_tok_new = Pcoq.Parsable.loc doc_handle in
        match res with
        | Ok { res = state; feedback } ->
          (* let goals = Coq.State.goals *)
          let diags =
            if !Config.v.ok_diagnostics then
              let ok_diag = mk_diag ast_loc 3 (Pp.str "OK") in
              [ ok_diag ]
            else []
          in
          let fb_diags = process_feedback ~loc:ast_loc feedback in
          let diags = parsing_diags @ fb_diags @ diags in
          let node =
            { loc = ast_loc; ast = Some ast; diags; state; memo_info }
          in
          let doc = add_node ~node doc in
          stm doc state last_tok_new
        | Error (err_loc, msg) ->
          let err_loc = Option.default ast_loc err_loc in
          let diags = [ mk_error_diagnostic ~loc:err_loc ~msg ~ast ] in
          (* FB should be handled by Coq.Protect.eval XXX *)
          let fb_diags = List.rev !fb_queue |> process_feedback ~loc:err_loc in
          fb_queue := [];
          let diags = parsing_diags @ fb_diags @ diags in
          let st = state_recovery_heuristic st ast in
          let node =
            { loc = ast_loc; ast = Some ast; diags; state = st; memo_info }
          in
          let doc = add_node ~node doc in
          stm doc st last_tok_new))
  in
  (* Note that nodes and diags in reversed order here *)
  let st =
    hd_opt ~default:doc.root (List.map (fun { state; _ } -> state) doc.nodes)
  in
  stm doc st last_tok

let print_stats () =
  (if !Config.v.mem_stats then
   let size = Memo.mem_stats () in
   Io.Log.error "stats" (string_of_int size));

  Io.Log.error "cache" (Stats.dump ());
  Io.Log.error "cache" (Memo.CacheStats.stats ());
  (* this requires patches to Coq *)
  (* Io.Log.error "coq parsing" (Cstats.dump ()); *)
  (* Cstats.reset (); *)
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

let log_resume last_tok =
  Io.Log.error "check"
    Format.(
      asprintf "resuming, from: %d l: %d" last_tok.Loc.ep
        last_tok.Loc.line_nb_last)

let check ~ofmt:_ ~doc ~fb_queue =
  match doc.completed with
  | Yes ->
    Io.Log.error "check" "resuming, completed=yes, nothing to do";
    doc
  | Stopped last_tok ->
    log_resume last_tok;
    let uri, version, contents = (doc.uri, doc.version, doc.contents) in
    (* Process markdown *)
    let processed_content = process_contents ~uri ~contents in
    (* Compute resume point, basically [CLexer.after] + stream setup *)
    let resume_loc = CLexer.after last_tok in
    let offset = resume_loc.bp in
    let processed_content =
      String.(sub processed_content offset (length processed_content - offset))
    in
    let handle =
      Pcoq.Parsable.make ~loc:resume_loc
        Gramlib.Stream.(of_string ~offset processed_content)
    in
    (* Set the document to "internal" mode *)
    let doc =
      { doc with contents = processed_content; nodes = List.rev doc.nodes }
    in
    let doc = process_and_parse ~uri ~version ~fb_queue doc last_tok handle in
    (* Set the document to "finished" mode: Restore the original contents,
       reverse the accumulators *)
    let doc = { doc with nodes = List.rev doc.nodes; contents } in
    let end_msg =
      match doc.completed with
      | Yes ->
        "done: document fully checked "
        ^ Pp.string_of_ppcmds (Loc.pr (Pcoq.Parsable.loc handle))
      | Stopped loc -> "done: stopped at " ^ Pp.string_of_ppcmds (Loc.pr loc)
    in
    Io.Log.error "check" end_msg;
    print_stats ();
    doc
