(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2022 Inria           -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

(* Should be moved to the right place *)
module Util = struct
  let hd_opt ~default l =
    match l with
    | [] -> default
    | h :: _ -> h

  let mk_diag ?(extra = []) range severity message =
    let range = Types.to_range range in
    let message = Pp.string_of_ppcmds message in
    Types.Diagnostic.{ range; severity; message; extra }

  (* ast-dependent error diagnostic generation *)
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

  let diags_of_feedback ~loc fbs =
    let diags, messages = List.partition (fun (_, lvl, _) -> lvl < 3) fbs in
    let diags =
      if !Config.v.show_notices_as_diagnostics then
        diags @ List.filter (fun (_, lvl, _) -> lvl = 3) fbs
      else diags
    in
    (List.map (feed_to_diag ~loc) diags, messages)

  let build_span start_loc end_loc =
    Loc.
      { start_loc with
        line_nb_last = end_loc.line_nb_last
      ; bol_pos_last = end_loc.bol_pos_last
      ; ep = end_loc.ep
      }

  let print_stats () =
    (if !Config.v.mem_stats then
     let size = Memo.mem_stats () in
     Io.Log.trace "stats" (string_of_int size));

    Io.Log.trace "cache" (Stats.to_string ());
    Io.Log.trace "cache" (Memo.CacheStats.stats ());
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

  let safe_sub s pos len =
    if pos < 0 || len < 0 || pos > String.length s - len then (
      let s = String.sub s 0 (Stdlib.min 20 String.(length s - 1)) in
      Io.Log.trace "string_sub"
        (Format.asprintf "error for pos: %d len: %d str: %s" pos len s);
      None)
    else Some (String.sub s pos len)

  let pp_words fmt w =
    if w < 1024.0 then Format.fprintf fmt "%.0f  w" w
    else if w < 1024.0 *. 1024.0 then Format.fprintf fmt "%.2f Kw" (w /. 1024.0)
    else Format.fprintf fmt "%.2f Mw" (w /. (1024.0 *. 1024.0))
end

module DDebug = struct
  let parsed_sentence ~ast =
    let loc = Coq.Ast.loc ast |> Option.get in
    let line = "[l: " ^ string_of_int (loc.Loc.line_nb - 1) ^ "] " in
    Io.Log.trace "coq"
      ("parsed sentence: " ^ line ^ Pp.string_of_ppcmds (Coq.Ast.print ast))

  let resume last_tok version =
    Io.Log.trace "check"
      Format.(
        asprintf "resuming [v: %d], from: %d l: %d" version last_tok.Loc.ep
          (last_tok.Loc.line_nb_last - 1))
end

(* [node list] is a very crude form of a meta-data map "loc -> data" , where for
   now [data] is only the goals. *)
module Node = struct
  module Info = struct
    type t =
      { cache_hit : bool
      ; parsing_time : float
      ; time : float option
      ; mw_prev : float
      ; mw_after : float
      }

    let make ?(cache_hit = false) ~parsing_time ?time ~mw_prev ~mw_after () =
      { cache_hit; parsing_time; time; mw_prev; mw_after }

    (* let { Gc.major_words = mw_after; _ } = Gc.quick_stat () in *)

    let pp_time fmt = function
      | None -> Format.fprintf fmt "N/A"
      | Some time -> Format.fprintf fmt "%.4f" time

    let print ~stats { cache_hit; parsing_time; time; mw_prev; mw_after } =
      let cptime = Stats.get_f stats ~kind:Stats.Kind.Parsing in
      let cetime = Stats.get_f stats ~kind:Stats.Kind.Exec in
      let memo_info =
        Format.asprintf
          "Cache Hit: %b | Parse (s/c): %.4f / %.2f | Exec (s/c): %a / %.2f"
          cache_hit parsing_time cptime pp_time time cetime
      in
      let mem_info =
        Format.asprintf "major words: %a | diff %a" Util.pp_words mw_after
          Util.pp_words (mw_after -. mw_prev)
      in
      memo_info ^ "\n___\n" ^ mem_info
  end

  type t =
    { loc : Loc.t
    ; ast : Coq.Ast.t option  (** Ast of node *)
    ; state : Coq.State.t  (** (Full) State of node *)
    ; diags : Types.Diagnostic.t list
    ; messages : Coq.Message.t list
    ; info : Info.t
    }

  let loc { loc; _ } = loc
  let ast { ast; _ } = ast
  let state { state; _ } = state
  let diags { diags; _ } = diags
  let messages { messages; _ } = messages
  let info { info; _ } = info
end

module Completion = struct
  type t =
    | Yes of Loc.t  (** Location of the last token in the document *)
    | Stopped of Loc.t  (** Location of the last valid token *)
    | Failed of Loc.t  (** Critical failure, like an anomaly *)

  let loc = function
    | Yes loc | Stopped loc | Failed loc -> loc
end

(* Private. A doc is a list of nodes for now. The first element in the list is
   assumed to be the tip of the document. The initial document is the empty
   list. *)
type t =
  { uri : string
  ; version : int
  ; contents : string
  ; end_loc : Types.Point.t
  ; root : Coq.State.t
  ; nodes : Node.t list
  ; diags_dirty : bool  (** Used to optimize `eager_diagnostics` *)
  ; completed : Completion.t
  ; stats : Stats.t  (** Info about cumulative stats *)
  }

let mk_doc root_state workspace =
  (* XXX This shouldn't be foo *)
  let libname = Names.(DirPath.make [ Id.of_string "foo" ]) in
  Coq.Init.doc_init ~root_state ~workspace ~libname

let init_loc ~uri = Loc.initial (InFile { dirpath = None; file = uri })

let get_last_text text =
  let lines = CString.split_on_char '\n' text in
  let last_line = Util.hd_opt ~default:"" (List.rev lines) in
  Types.Point.
    { line = List.length lines - 1
    ; character = String.length last_line
    ; offset = String.length text
    }

let process_init_feedback loc state feedback =
  if not (CList.is_empty feedback) then
    let diags, messages = Util.diags_of_feedback ~loc feedback in
    let parsing_time = 0.0 in
    let { Gc.major_words = mw_prev; _ } = Gc.quick_stat () in
    let info = Node.Info.make ~parsing_time ~mw_prev ~mw_after:mw_prev () in
    [ { Node.loc; ast = None; state; diags; messages; info } ]
  else []

let create ~state ~workspace ~uri ~version ~contents =
  let { Coq.Protect.E.r; feedback } = mk_doc state workspace in
  Coq.Protect.R.map r ~f:(fun root ->
      Stats.reset ();
      let stats = Stats.dump () in
      let init_loc = init_loc ~uri in
      let nodes = process_init_feedback init_loc root feedback in
      let diags_dirty = not (CList.is_empty nodes) in
      let end_loc = get_last_text contents in
      { uri
      ; contents
      ; end_loc
      ; version
      ; root
      ; nodes
      ; diags_dirty
      ; completed = Stopped init_loc
      ; stats
      })

let recover_up_to_offset doc offset =
  Io.Log.trace "prefix"
    (Format.asprintf "common prefix offset found at %d" offset);
  let rec find acc_nodes acc_loc nodes =
    match nodes with
    | [] -> (List.rev acc_nodes, acc_loc)
    | n :: ns ->
      if Debug.scan then
        Io.Log.trace "scan"
          (Format.asprintf "consider node at %s" (Coq.Ast.pr_loc n.Node.loc));
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
  Io.Log.trace "prefix" ("resuming from " ^ Coq.Ast.pr_loc loc);
  let completed = Completion.Stopped loc in
  (nodes, completed)

let bump_version ~version ~contents ~end_loc doc =
  (* When a new document, we resume checking from a common prefix *)
  let nodes, completed = compute_common_prefix ~contents doc in
  { doc with
    version
  ; nodes
  ; contents
  ; end_loc
  ; diags_dirty = true (* EJGA: Is it worth to optimize this? *)
  ; completed
  }

let bump_version ~version ~contents doc =
  let end_loc = get_last_text contents in
  match doc.completed with
  (* We can do better, but we need to handle the case where the anomaly is when
     restoring / executing the first sentence *)
  | Failed _ ->
    { doc with
      version
    ; nodes = []
    ; contents
    ; end_loc
    ; diags_dirty = true
    ; completed = Stopped (init_loc ~uri:doc.uri)
    }
  | Stopped _ | Yes _ -> bump_version ~version ~contents ~end_loc doc

let add_node ~node doc =
  let diags_dirty = if node.Node.diags <> [] then true else doc.diags_dirty in
  { doc with nodes = node :: doc.nodes; diags_dirty }

let concat_diags doc = List.concat_map (fun node -> node.Node.diags) doc.nodes

let send_eager_diagnostics ~ofmt ~uri ~version ~doc =
  (* this is too noisy *)
  (* let proc_diag = mk_diag loc 3 (Pp.str "Processing") in *)
  (* Io.Report.diagnostics ~uri ~version (proc_diag :: doc.diags)); *)
  if doc.diags_dirty && !Config.v.eager_diagnostics then (
    let diags = concat_diags doc in
    Io.Report.diagnostics ~ofmt ~uri ~version diags;
    { doc with diags_dirty = false })
  else doc

let set_completion ~completed doc = { doc with completed }
let set_stats ~stats doc = { doc with stats }

(* We approximate the remnants of the document. It would be easier if instead of
   reporting what is missing, we would report what is done, but for now we are
   trying this paradigm.

   As we are quite dynamic (for now) in terms of what we observe of the document
   (basically we observe it linearly), we must compute the final position with a
   bit of a hack. *)
let compute_progress end_ last_done =
  let start =
    { Types.Point.line = last_done.Loc.line_nb_last - 1
    ; character = last_done.ep - last_done.bol_pos_last
    ; offset = last_done.ep
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
  let f ps = Coq.Parsing.parse ~st ps in
  Stats.record ~kind:Stats.Kind.Parsing ~f ps

let rec find_recovery_for_failed_qed ~default nodes =
  match nodes with
  | [] -> (default, None)
  | { Node.ast = None; _ } :: ns -> find_recovery_for_failed_qed ~default ns
  | { ast = Some ast; state; loc; _ } :: ns -> (
    match (Coq.Ast.to_coq ast).CAst.v.Vernacexpr.expr with
    | Vernacexpr.VernacStartTheoremProof _ -> (
      if !Config.v.admit_on_bad_qed then
        let state = Memo.interp_admitted ~st:state in
        (state, Some loc)
      else
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
    Io.Log.trace "recovery" (loc_msg ^ " " ^ Memo.input_info (v, st));
    st
  | _ -> st

let interp_and_info ~parsing_time ~st ast =
  let { Gc.major_words = mw_prev; _ } = Gc.quick_stat () in
  (* memo memory stats are disabled: slow and misleading *)
  let { Memo.Stats.res; cache_hit; memory = _; time } =
    Memo.interp_command ~st ast
  in
  let { Gc.major_words = mw_after; _ } = Gc.quick_stat () in
  let info =
    Node.Info.make ~cache_hit ~parsing_time ~time ~mw_prev ~mw_after ()
  in
  (res, info)

(* Copied from CLexer *)
let clexer_after loc =
  Loc.
    { loc with
      line_nb = loc.line_nb_last
    ; bol_pos = loc.bol_pos_last
    ; bp = loc.ep
    }

type parse_action =
  | EOF of Completion.t (* completed *)
  | Skip of Loc.t * Loc.t (* span of the skipped sentence + last valid token *)
  | Process of Coq.Ast.t (* success! *)

(* Returns parse_action, diags, parsing_time *)
let parse_action ~st last_tok doc_handle =
  let start_loc = Coq.Parsing.Parsable.loc doc_handle |> clexer_after in
  let { Coq.Protect.E.r; feedback }, time = parse_stm ~st doc_handle in
  match r with
  | Coq.Protect.R.Interrupted -> (EOF (Stopped last_tok), [], feedback, time)
  | Coq.Protect.R.Completed res -> (
    match res with
    | Ok None ->
      (* We actually need to fix Coq to return the location of the true file
         EOF, the below trick doesn't work. That will involved updating the type
         of `main_entry` *)
      let last_tok = Coq.Parsing.Parsable.loc doc_handle in
      (EOF (Yes last_tok), [], feedback, time)
    | Ok (Some ast) ->
      let () = if Debug.parsing then DDebug.parsed_sentence ~ast in
      (Process ast, [], feedback, time)
    | Error (Anomaly (_, msg)) | Error (User (None, msg)) ->
      (* We don't have a better altenative :(, usually missing error loc here
         means an anomaly, so we stop *)
      let err_loc = last_tok in
      let parse_diags = [ Util.mk_diag err_loc 1 msg ] in
      (EOF (Failed last_tok), parse_diags, feedback, time)
    | Error (User (Some err_loc, msg)) ->
      let parse_diags = [ Util.mk_diag err_loc 1 msg ] in
      Coq.Parsing.discard_to_dot doc_handle;
      let last_tok = Coq.Parsing.Parsable.loc doc_handle in
      let span_loc = Util.build_span start_loc last_tok in
      (Skip (span_loc, last_tok), parse_diags, feedback, time))

(* Result of node-building action *)
type document_action =
  | Stop of Completion.t * Node.t
  | Continue of
      { state : Coq.State.t
      ; last_tok : Loc.t
      ; node : Node.t
      }
  | Interrupted of Loc.t

let unparseable_node ~loc ~parsing_diags ~parsing_feedback ~state ~parsing_time
    =
  let fb_diags, messages = Util.diags_of_feedback ~loc parsing_feedback in
  let diags = fb_diags @ parsing_diags in
  let { Gc.major_words = mw_prev; _ } = Gc.quick_stat () in
  let info = Node.Info.make ~parsing_time ~mw_prev ~mw_after:mw_prev () in
  { Node.loc; ast = None; diags; messages; state; info }

let assemble_diags ~loc ~parsing_diags ~parsing_feedback ~diags ~feedback =
  let parsing_fb_diags, parsing_messages =
    Util.diags_of_feedback ~loc parsing_feedback
  in
  let fb_diags, fb_messages = Util.diags_of_feedback ~loc feedback in
  let diags = parsing_diags @ parsing_fb_diags @ fb_diags @ diags in
  let messages = parsing_messages @ fb_messages in
  (diags, messages)

let parsed_node ~loc ~ast ~state ~parsing_diags ~parsing_feedback ~diags
    ~feedback ~info =
  let diags, messages =
    assemble_diags ~loc ~parsing_diags ~parsing_feedback ~diags ~feedback
  in
  { Node.loc; ast = Some ast; diags; messages; state; info }

let stream_of_string ~offset text =
  let pad = String.make offset ' ' in
  let str = Stream.of_string (pad ^ text) in
  for _i = 1 to offset do
    Stream.junk str
  done;
  str

let maybe_ok_diagnostics ~loc =
  if !Config.v.ok_diagnostics then
    let ok_diag = Util.mk_diag loc 3 (Pp.str "OK") in
    [ ok_diag ]
  else []

let strategy_of_coq_err ~node ~state ~last_tok = function
  | Coq.Protect.Error.Anomaly _ -> Stop (Failed last_tok, node)
  | User _ -> Continue { state; last_tok; node }

let node_of_coq_result ~doc ~parsing_diags ~parsing_feedback ~ast ~st ~feedback
    ~info last_tok res =
  let ast_loc = Coq.Ast.loc ast |> Option.get in
  match res with
  | Ok { Coq.Interp.Info.res = state } ->
    let ok_diags = maybe_ok_diagnostics ~loc:ast_loc in
    let node =
      parsed_node ~loc:ast_loc ~ast ~state ~parsing_diags ~parsing_feedback
        ~diags:ok_diags ~feedback ~info
    in
    Continue { state; last_tok; node }
  | Error (Coq.Protect.Error.Anomaly (err_loc, msg) as coq_err)
  | Error (User (err_loc, msg) as coq_err) ->
    let err_loc = Option.default ast_loc err_loc in
    let err_diags = [ Util.mk_error_diagnostic ~loc:err_loc ~msg ~ast ] in
    let recovery_st = state_recovery_heuristic doc st ast in
    let node =
      parsed_node ~loc:ast_loc ~ast ~state:recovery_st ~parsing_diags
        ~parsing_feedback ~diags:err_diags ~feedback ~info
    in
    strategy_of_coq_err ~node ~state:recovery_st ~last_tok coq_err

(* Build a document node, possibly executing *)
let document_action ~st ~parsing_diags ~parsing_feedback ~parsing_time ~doc
    last_tok doc_handle action =
  match action with
  (* End of file *)
  | EOF completed ->
    let loc = Completion.loc completed in
    let node =
      unparseable_node ~loc ~parsing_diags ~parsing_feedback ~state:st
        ~parsing_time
    in
    Stop (completed, node)
  (* Parsing error *)
  | Skip (span_loc, last_tok) ->
    let node =
      unparseable_node ~loc:span_loc ~parsing_diags ~parsing_feedback ~state:st
        ~parsing_time
    in
    Continue { state = st; last_tok; node }
  (* We can interpret the command now *)
  | Process ast -> (
    let { Coq.Protect.E.r; feedback }, info =
      interp_and_info ~parsing_time ~st ast
    in
    match r with
    | Coq.Protect.R.Interrupted ->
      (* Exit *)
      Interrupted last_tok
    | Coq.Protect.R.Completed res ->
      (* The evaluation by Coq fully completed, then we can resume checking from
         this point then, hence the new last valid token last_tok_new *)
      let last_tok_new = Coq.Parsing.Parsable.loc doc_handle in
      node_of_coq_result ~doc ~ast ~st ~parsing_diags ~parsing_feedback
        ~feedback ~info last_tok_new res)

module Target = struct
  type t =
    | End
    | Position of int * int
end

let beyond_target pos target =
  match target with
  | Target.End -> false
  | Position (cut_line, cut_col) ->
    (* This needs careful thinking as to help with the show goals postponement
       case. *)
    let pos_line = pos.Loc.line_nb_last - 1 in
    let pos_col = Loc.(pos.ep - pos.bol_pos_last) in
    pos_line > cut_line || (pos_line = cut_line && pos_col > cut_col)

let pr_target = function
  | Target.End -> "end"
  | Target.Position (l, c) -> Format.asprintf "{cutpoint l: %02d | c: %02d" l c

let log_beyond_target last_tok target =
  Io.Log.trace "beyond_target" ("target reached " ^ Coq.Ast.pr_loc last_tok);
  Io.Log.trace "beyond_target" ("target is " ^ pr_target target)

(* main interpretation loop *)
let process_and_parse ~ofmt ~target ~uri ~version doc last_tok doc_handle =
  let rec stm doc st last_tok =
    (* Reporting of progress and diagnostics (if dirty) *)
    let doc = send_eager_diagnostics ~ofmt ~uri ~version ~doc in
    report_progress ~ofmt ~doc last_tok;
    if Debug.parsing then Io.Log.trace "coq" "parsing sentence";
    if beyond_target last_tok target then
      let () = log_beyond_target last_tok target in
      (* We set to Completed.Yes when we have reached the EOI *)
      let completed =
        if last_tok.Loc.ep >= doc.end_loc.offset then Completion.Yes last_tok
        else Completion.Stopped last_tok
      in
      set_completion ~completed doc
    else
      (* Parsing *)
      let action, parsing_diags, parsing_feedback, parsing_time =
        parse_action ~st last_tok doc_handle
      in
      (* Execution *)
      let action =
        document_action ~st ~parsing_diags ~parsing_feedback ~parsing_time ~doc
          last_tok doc_handle action
      in
      match action with
      | Interrupted last_tok -> set_completion ~completed:(Stopped last_tok) doc
      | Stop (completed, node) ->
        let doc = add_node ~node doc in
        set_completion ~completed doc
      | Continue { state; last_tok; node } ->
        let doc = add_node ~node doc in
        stm doc state last_tok
  in
  (* Set the document to "internal" mode, stm expects the node list to be in
     reveresed order *)
  let doc = { doc with nodes = List.rev doc.nodes } in
  (* Note that nodes and diags in reversed order here *)
  (match doc.nodes with
  | [] -> ()
  | n :: _ -> Io.Log.trace "resume" ("last node :" ^ Coq.Ast.pr_loc n.loc));
  let st =
    Util.hd_opt ~default:doc.root
      (List.map (fun { Node.state; _ } -> state) doc.nodes)
  in
  Stats.restore doc.stats;
  let doc = stm doc st last_tok in
  let stats = Stats.dump () in
  let doc = set_stats ~stats doc in
  (* Set the document to "finished" mode: reverse the node list *)
  let doc = { doc with nodes = List.rev doc.nodes } in
  doc

let log_doc_completion (completed : Completion.t) =
  let timestamp = Unix.gettimeofday () in
  let loc, status =
    match completed with
    | Yes loc -> (loc, "fully checked")
    | Stopped loc -> (loc, "stopped")
    | Failed loc -> (loc, "failed")
  in
  Format.asprintf "done [%.2f]: document %s with pos %s" timestamp status
    (Coq.Ast.pr_loc loc)
  |> Io.Log.trace "check"

let resume_check ~ofmt ~last_tok ~doc ~target =
  let uri, version, contents = (doc.uri, doc.version, doc.contents) in
  (* Process markdown *)
  let processed_content = Util.process_contents ~uri ~contents in
  (* Compute resume point, basically [CLexer.after] + stream setup *)
  let resume_loc = clexer_after last_tok in
  let offset = resume_loc.bp in
  Coq.Parsing.bp_ := resume_loc.bp;
  let pcontent_len = String.length processed_content in
  match Util.safe_sub processed_content offset (pcontent_len - offset) with
  | None ->
    (* Guard against internal tricky eof errors *)
    let completed = Completion.Failed last_tok in
    set_completion ~completed doc
  | Some processed_content ->
    let handle =
      Coq.Parsing.Parsable.make ~loc:resume_loc
        (stream_of_string ~offset processed_content)
    in
    (* Set the content to the padded version if neccesary *)
    let doc = { doc with contents = processed_content } in
    let doc =
      process_and_parse ~ofmt ~target ~uri ~version doc last_tok handle
    in
    (* Restore the original contents *)
    { doc with contents }

let check ~ofmt ~target ~doc () =
  match doc.completed with
  | Yes _ ->
    Io.Log.trace "check" "resuming, completed=yes, nothing to do";
    doc
  | Failed _ ->
    Io.Log.trace "check" "can't resume, failed=yes, nothing to do";
    doc
  | Stopped last_tok ->
    DDebug.resume last_tok doc.version;
    let doc = resume_check ~ofmt ~last_tok ~doc ~target in
    log_doc_completion doc.completed;
    Util.print_stats ();
    doc
