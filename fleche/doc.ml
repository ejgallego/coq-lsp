(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2022 Inria           -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

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
    | Yes of Loc.t  (** Location of the last token in the document *)
    | Stopped of Loc.t  (** Location of the last valid token *)
end

(* Private. A doc is a list of nodes for now. The first element in the list is
   assumed to be the tip of the document. The initial document is the empty
   list. *)
type t =
  { uri : string
  ; version : int
  ; contents : string
  ; end_loc : int * int * int
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

let get_last_text text =
  let lines = CString.split_on_char '\n' text in
  let last_line = hd_opt ~default:"" (List.rev lines) in
  (List.length lines, String.length last_line, String.length text)

let create ~state ~workspace ~uri ~version ~contents =
  let end_loc = get_last_text contents in
  { uri
  ; contents
  ; end_loc
  ; version
  ; root = mk_doc state workspace
  ; nodes = []
  ; diags_dirty = false
  ; completed = Stopped (init_loc ~uri)
  }

let recover_up_to_offset doc offset =
  Io.Log.error "prefix"
    (Format.asprintf "common prefix offset found at %d" offset);
  let rec find acc_nodes acc_loc nodes =
    match nodes with
    | [] -> (List.rev acc_nodes, acc_loc)
    | n :: ns ->
      Io.Log.error "scan"
        (Format.asprintf "consider node at %s" (Coq.Ast.pr_loc n.loc));
      if n.loc.Loc.ep >= offset then (List.rev acc_nodes, acc_loc)
      else find (n :: acc_nodes) n.loc ns
  in
  let loc = init_loc ~uri:doc.uri in
  find [] loc doc.nodes

let compute_common_prefix ~contents doc =
  let s1 = doc.contents in
  let l1 = String.length s1 in
  let s2 = contents in
  let l2 = String.length s2 in
  let rec match_or_stop i =
    if i = l1 || i = l2 then i
    else if Char.equal s1.[i] s2.[i] then match_or_stop (i + 1)
    else i
  in
  let common_idx = match_or_stop 0 in
  let nodes, loc = recover_up_to_offset doc common_idx in
  Io.Log.error "prefix" ("resuming from " ^ Coq.Ast.pr_loc loc);
  let completed = Completion.Stopped loc in
  (nodes, completed)

let bump_version ~version ~contents doc =
  (* When a new document, we resume checking from a common prefix *)
  let nodes, completed = compute_common_prefix ~contents doc in
  let end_loc = get_last_text contents in
  { doc with
    version
  ; nodes
  ; contents
  ; end_loc
  ; diags_dirty = true (* EJGA: Is it worth to optimize this? *)
  ; completed
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

(* We approximate the remnants of the document. It would be easier if instead of
   reporting what is missing, we would report what is done, but for now we are
   trying this paradigm.

   As we are quite dynamic (for now) in terms of what we observe of the document
   (basically we observe it linearly), we must compute the final position with a
   bit of a hack. *)
let compute_progress end_loc last_done =
  let start =
    { Types.Point.line = last_done.Loc.line_nb_last - 1
    ; character = last_done.ep - last_done.bol_pos_last
    ; offset = last_done.ep
    }
  in
  let end_line, end_col, end_offset = end_loc in
  let end_ =
    { Types.Point.line = end_line - 1
    ; character = end_col
    ; offset = end_offset
    }
  in
  let range = Types.Range.{ start; end_ } in
  (range, 1)

let report_progress ~doc last_tok =
  let progress = compute_progress doc.end_loc last_tok in
  Io.Report.fileProgress ~uri:doc.uri ~version:doc.version [ progress ]

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
    | Tok.KEYWORD ("." | "..." | "end" | "Qed" | "Defined" | "Admitted") -> ()
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

let rec find_recovery_for_failed_qed ~default nodes =
  match nodes with
  | [] -> (default, None)
  | { ast = None; _ } :: ns -> find_recovery_for_failed_qed ~default ns
  | { ast = Some ast; state = _; _ } :: ns -> (
    match (Coq.Ast.to_coq ast).CAst.v.Vernacexpr.expr with
    | Vernacexpr.VernacStartTheoremProof _ -> (
      match ns with
      | [] -> (default, None)
      | n :: _ -> (n.state, Some n.loc))
    | _ -> find_recovery_for_failed_qed ~default ns)

(* Simple heuristic for Qed. *)
let state_recovery_heuristic doc st v =
  match (Coq.Ast.to_coq v).CAst.v.Vernacexpr.expr with
  (* Drop the top proof state if we reach a faulty Qed. *)
  | Vernacexpr.VernacEndProof _ ->
    let st, loc = find_recovery_for_failed_qed ~default:st doc.nodes in
    let loc_msg = Option.cata Coq.Ast.pr_loc "no loc" loc in
    Io.Log.error "recovery" (loc_msg ^ " " ^ Memo.input_info (v, st));
    st
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
    report_progress ~doc last_tok;
    if Debug.parsing then Io.Log.error "coq" "parsing sentence";
    (* Parsing *)
    let action, parsing_diags, parsing_time =
      let start_loc = Pcoq.Parsable.loc doc_handle |> CLexer.after in
      match parse_stm ~st doc_handle with
      | Coq.Protect.R.Interrupted, time -> (EOF (Stopped last_tok), [], time)
      | Coq.Protect.R.Completed res, time -> (
        match res with
        | Ok None ->
          (* We actually need to fix Coq to return the location of the true file
             EOF, the below trick doesn't work. That will involved updating the
             type of `main_entry` *)
          let last_tok = Pcoq.Parsable.loc doc_handle in
          (EOF (Yes last_tok), [], time)
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
          let st = state_recovery_heuristic doc st ast in
          let node =
            { loc = ast_loc; ast = Some ast; diags; state = st; memo_info }
          in
          let doc = add_node ~node doc in
          stm doc st last_tok_new))
  in
  (* Note that nodes and diags in reversed order here *)
  (match doc.nodes with
  | [] -> ()
  | n :: _ -> Io.Log.error "resume" ("last node :" ^ Coq.Ast.pr_loc n.loc));
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
  | Yes _ ->
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
      let timestamp = Unix.gettimeofday () in
      let loc =
        match doc.completed with
        | Yes loc -> loc
        | Stopped loc -> loc
      in
      Format.asprintf "done [%.2f]: document fully checked %a" timestamp
        Pp.pp_with (Loc.pr loc)
    in
    Io.Log.error "check" end_msg;
    print_stats ();
    doc
