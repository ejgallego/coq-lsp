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

  let mk_diag ?extra range severity message =
    let message = Pp.string_of_ppcmds message in
    Types.Diagnostic.{ range; severity; message; extra }

  (* ast-dependent error diagnostic generation *)
  let mk_error_diagnostic ~range ~msg ~ast =
    match (Coq.Ast.to_coq ast).v with
    | Vernacexpr.{ expr = VernacRequire (prefix, _export, module_refs); _ } ->
      let refs = List.map fst module_refs in
      let extra =
        Some [ Types.Diagnostic.Extra.FailedRequire { prefix; refs } ]
      in
      mk_diag ?extra range 1 msg
    | _ -> mk_diag range 1 msg

  let feed_to_diag ~drange (range, severity, message) =
    let range = Option.default drange range in
    mk_diag range severity message

  let diags_of_messages ~drange fbs =
    let diags, messages = List.partition (fun (_, lvl, _) -> lvl < 3) fbs in
    let diags =
      if !Config.v.show_notices_as_diagnostics then
        diags @ List.filter (fun (_, lvl, _) -> lvl = 3) fbs
      else diags
    in
    (List.map (feed_to_diag ~drange) diags, messages)

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
    (* Io.Log.error "coq parsing" (CoqParsingStats.dump ()); *)
    (* CoqParsingStats.reset (); *)
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

  let resume (last_tok : Types.Range.t) version =
    Io.Log.trace "check"
      Format.(
        asprintf "resuming [v: %d], from: %d l: %d" version last_tok.end_.offset
          last_tok.end_.line)
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

  module Message = struct
    type t = Types.Range.t option * int * Pp.t

    let feedback_to_message ~lines (loc, lvl, msg) =
      (Coq_utils.to_orange ~lines loc, lvl, msg)
  end

  type t =
    { range : Types.Range.t
    ; ast : Coq.Ast.t option  (** Ast of node *)
    ; state : Coq.State.t  (** (Full) State of node *)
    ; diags : Types.Diagnostic.t list
    ; messages : Message.t list
    ; info : Info.t
    }

  let range { range; _ } = range
  let ast { ast; _ } = ast
  let state { state; _ } = state
  let diags { diags; _ } = diags
  let messages { messages; _ } = messages
  let info { info; _ } = info
end

module Contents = struct
  type t =
    { raw : string  (** That's the original, unprocessed document text *)
    ; text : string
          (** That's the text to be sent to the prover, already processed,
              encoded in UTF-8 *)
    ; last : Types.Point.t
          (** Last point of [text], you can derive n_lines from here *)
    ; lines : string Array.t  (** [text] split in lines *)
    }

  let get_last_text text =
    let offset = String.length text in
    let lines = CString.split_on_char '\n' text |> Array.of_list in
    let n_lines = Array.length lines in
    let last_line = if n_lines < 1 then "" else Array.get lines (n_lines - 1) in
    let last_line_col = String.length last_line in
    let character = Utf8.char_of_byte ~line:last_line ~byte:last_line_col in
    (Types.Point.{ line = n_lines - 1; character; offset }, lines)

  let make ~uri ~raw =
    let text = Util.process_contents ~uri ~contents:raw in
    let last, lines = get_last_text text in
    { raw; text; last; lines }
end

module Completion = struct
  type t =
    | Yes of Types.Range.t  (** Location of the last token in the document *)
    | Stopped of Types.Range.t  (** Location of the last valid token *)
    | Failed of Types.Range.t  (** Critical failure, like an anomaly *)

  let range = function
    | Yes range | Stopped range | Failed range -> range

  let to_string = function
    | Yes _ -> "fully checked"
    | Stopped _ -> "stopped"
    | Failed _ -> "failed"
end

(* Private. A doc is a list of nodes for now. The first element in the list is
   assumed to be the tip of the document. The initial document is the empty
   list. *)
type t =
  { uri : string
  ; version : int
  ; contents : Contents.t
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

let init_fname ~uri = Loc.InFile { dirpath = None; file = uri }
let init_loc ~uri = Loc.initial (init_fname ~uri)

let process_init_feedback range state messages =
  if not (CList.is_empty messages) then
    let diags, messages = Util.diags_of_messages ~drange:range messages in
    let parsing_time = 0.0 in
    let { Gc.major_words = mw_prev; _ } = Gc.quick_stat () in
    let info = Node.Info.make ~parsing_time ~mw_prev ~mw_after:mw_prev () in
    [ { Node.range; ast = None; state; diags; messages; info } ]
  else []

let create ~state ~workspace ~uri ~version ~contents =
  let { Coq.Protect.E.r; feedback } = mk_doc state workspace in
  Coq.Protect.R.map r ~f:(fun root ->
      let stats = Stats.zero () in
      let init_loc = init_loc ~uri in
      let contents = Contents.make ~uri ~raw:contents in
      let lines = contents.lines in
      let init_range = Coq_utils.to_range ~lines init_loc in
      let feedback =
        List.map (Node.Message.feedback_to_message ~lines) feedback
      in
      let nodes = process_init_feedback init_range root feedback in
      let diags_dirty = not (CList.is_empty nodes) in
      { uri
      ; contents
      ; version
      ; root
      ; nodes
      ; diags_dirty
      ; completed = Stopped init_range
      ; stats
      })

let recover_up_to_offset ~init_range doc offset =
  Io.Log.trace "prefix"
    (Format.asprintf "common prefix offset found at %d" offset);
  let rec find acc_nodes acc_range nodes =
    match nodes with
    | [] -> (List.rev acc_nodes, acc_range)
    | n :: ns ->
      if Debug.scan then
        Io.Log.trace "scan"
          (Format.asprintf "consider node at %a" Types.Range.pp n.Node.range);
      if n.range.end_.offset >= offset then (List.rev acc_nodes, acc_range)
      else find (n :: acc_nodes) n.range ns
  in
  find [] init_range doc.nodes

let compute_common_prefix ~init_range ~contents (prev : t) =
  let s1 = prev.contents.raw in
  let l1 = prev.contents.last.offset in
  let s2 = contents.Contents.raw in
  let l2 = contents.last.offset in
  let rec match_or_stop i =
    if i = l1 || i = l2 then i
    else if Char.equal s1.[i] s2.[i] then match_or_stop (i + 1)
    else i
  in
  let common_idx = match_or_stop 0 in
  let nodes, range = recover_up_to_offset ~init_range prev common_idx in
  Io.Log.trace "prefix" ("resuming from " ^ Types.Range.to_string range);
  let completed = Completion.Stopped range in
  (nodes, completed)

let bump_version ~init_range ~version ~contents doc =
  (* When a new document, we resume checking from a common prefix *)
  let nodes, completed = compute_common_prefix ~init_range ~contents doc in
  (* uri, root_state, and stats remain the same, stats should not! *)
  (* XXX: make the stats structure incremental *)
  let stats = doc.stats in
  { doc with
    version
  ; nodes
  ; contents
  ; diags_dirty = true (* EJGA: Is it worth to optimize this? *)
  ; completed
  ; stats
  }

let bump_version ~version ~contents doc =
  let contents = Contents.make ~uri:doc.uri ~raw:contents in
  let init_loc = init_loc ~uri:doc.uri in
  let init_range = Coq_utils.to_range ~lines:contents.lines init_loc in
  match doc.completed with
  (* We can do better, but we need to handle the case where the anomaly is when
     restoring / executing the first sentence *)
  | Failed _ ->
    { doc with
      version
    ; nodes = []
    ; contents
    ; diags_dirty = true
    ; completed = Stopped init_range
    }
  | Stopped _ | Yes _ -> bump_version ~init_range ~version ~contents doc

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
let compute_progress end_ (last_done : Types.Range.t) =
  let start = last_done.end_ in
  let range = Types.Range.{ start; end_ } in
  { Progress.Info.range; kind = 1 }

let report_progress ~doc (last_tok : Types.Range.t) =
  let progress = compute_progress doc.contents.last last_tok in
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
  | { ast = Some ast; state; range; _ } :: ns -> (
    match (Coq.Ast.to_coq ast).CAst.v.Vernacexpr.expr with
    | Vernacexpr.VernacStartTheoremProof _ -> (
      if !Config.v.admit_on_bad_qed then
        let state = Memo.interp_admitted ~st:state in
        (state, Some range)
      else
        match ns with
        | [] -> (default, None)
        | n :: _ -> (n.state, Some n.range))
    | _ -> find_recovery_for_failed_qed ~default ns)

(* Simple heuristic for Qed. *)
let state_recovery_heuristic doc st v =
  match (Coq.Ast.to_coq v).CAst.v.Vernacexpr.expr with
  (* Drop the top proof state if we reach a faulty Qed. *)
  | Vernacexpr.VernacEndProof _ ->
    let st, range = find_recovery_for_failed_qed ~default:st doc.nodes in
    let loc_msg = Option.cata Types.Range.to_string "no loc" range in
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

type parse_action =
  | EOF of Completion.t (* completed *)
  | Skip of
      Types.Range.t
      * Types.Range.t (* span of the skipped sentence + last valid token *)
  | Process of Coq.Ast.t (* success! *)

(* Returns parse_action, diags, parsing_time *)
let parse_action ~lines ~st last_tok doc_handle =
  let start_loc = Coq.Parsing.Parsable.loc doc_handle |> CLexer.after in
  let parse_res, time = parse_stm ~st doc_handle in
  let f = Coq_utils.to_range ~lines in
  let { Coq.Protect.E.r; feedback } = Coq.Protect.E.map_loc ~f parse_res in
  match r with
  | Coq.Protect.R.Interrupted -> (EOF (Stopped last_tok), [], feedback, time)
  | Coq.Protect.R.Completed res -> (
    match res with
    | Ok None ->
      (* We actually need to fix Coq to return the location of the true file
         EOF, the below trick doesn't work. That will involved updating the type
         of `main_entry` *)
      let last_tok = Coq.Parsing.Parsable.loc doc_handle in
      let last_tok = Coq_utils.to_range ~lines last_tok in
      (EOF (Yes last_tok), [], feedback, time)
    | Ok (Some ast) ->
      let () = if Debug.parsing then DDebug.parsed_sentence ~ast in
      (Process ast, [], feedback, time)
    | Error (Anomaly (_, msg)) | Error (User (None, msg)) ->
      (* We don't have a better altenative :(, usually missing error loc here
         means an anomaly, so we stop *)
      let err_range = last_tok in
      let parse_diags = [ Util.mk_diag err_range 1 msg ] in
      (EOF (Failed last_tok), parse_diags, feedback, time)
    | Error (User (Some err_range, msg)) ->
      let parse_diags = [ Util.mk_diag err_range 1 msg ] in
      Coq.Parsing.discard_to_dot doc_handle;
      let last_tok = Coq.Parsing.Parsable.loc doc_handle in
      let last_tok_range = Coq_utils.to_range ~lines last_tok in
      let span_loc = Util.build_span start_loc last_tok in
      let span_range = Coq_utils.to_range ~lines span_loc in
      (Skip (span_range, last_tok_range), parse_diags, feedback, time))

(* Result of node-building action *)
type document_action =
  | Stop of Completion.t * Node.t
  | Continue of
      { state : Coq.State.t
      ; last_tok : Types.Range.t
      ; node : Node.t
      }
  | Interrupted of Types.Range.t

let unparseable_node ~range ~parsing_diags ~parsing_feedback ~state
    ~parsing_time =
  let fb_diags, messages =
    Util.diags_of_messages ~drange:range parsing_feedback
  in
  let diags = fb_diags @ parsing_diags in
  let { Gc.major_words = mw_prev; _ } = Gc.quick_stat () in
  let info = Node.Info.make ~parsing_time ~mw_prev ~mw_after:mw_prev () in
  { Node.range; ast = None; diags; messages; state; info }

let assemble_diags ~range ~parsing_diags ~parsing_feedback ~diags ~feedback =
  let parsing_fb_diags, parsing_messages =
    Util.diags_of_messages ~drange:range parsing_feedback
  in
  let fb_diags, fb_messages = Util.diags_of_messages ~drange:range feedback in
  let diags = parsing_diags @ parsing_fb_diags @ fb_diags @ diags in
  let messages = parsing_messages @ fb_messages in
  (diags, messages)

let parsed_node ~range ~ast ~state ~parsing_diags ~parsing_feedback ~diags
    ~feedback ~info =
  let diags, messages =
    assemble_diags ~range ~parsing_diags ~parsing_feedback ~diags ~feedback
  in
  { Node.range; ast = Some ast; diags; messages; state; info }

let maybe_ok_diagnostics ~range =
  if !Config.v.ok_diagnostics then
    let ok_diag = Util.mk_diag range 3 (Pp.str "OK") in
    [ ok_diag ]
  else []

let strategy_of_coq_err ~node ~state ~last_tok = function
  | Coq.Protect.Error.Anomaly _ -> Stop (Failed last_tok, node)
  | User _ -> Continue { state; last_tok; node }

let node_of_coq_result ~doc ~range ~ast ~st ~parsing_diags ~parsing_feedback
    ~feedback ~info last_tok res =
  match res with
  | Ok { Coq.Interp.Info.res = state } ->
    let ok_diags = maybe_ok_diagnostics ~range in
    let node =
      parsed_node ~range ~ast ~state ~parsing_diags ~parsing_feedback
        ~diags:ok_diags ~feedback ~info
    in
    Continue { state; last_tok; node }
  | Error (Coq.Protect.Error.Anomaly (err_range, msg) as coq_err)
  | Error (User (err_range, msg) as coq_err) ->
    let err_range = Option.default range err_range in
    let err_diags = [ Util.mk_error_diagnostic ~range:err_range ~msg ~ast ] in
    let recovery_st = state_recovery_heuristic doc st ast in
    let node =
      parsed_node ~range ~ast ~state:recovery_st ~parsing_diags
        ~parsing_feedback ~diags:err_diags ~feedback ~info
    in
    strategy_of_coq_err ~node ~state:recovery_st ~last_tok coq_err

(* Build a document node, possibly executing *)
let document_action ~st ~parsing_diags ~parsing_feedback ~parsing_time ~doc
    last_tok doc_handle action =
  match action with
  (* End of file *)
  | EOF completed ->
    let range = Completion.range completed in
    let node =
      unparseable_node ~range ~parsing_diags ~parsing_feedback ~state:st
        ~parsing_time
    in
    Stop (completed, node)
  (* Parsing error *)
  | Skip (span_range, last_tok) ->
    let node =
      unparseable_node ~range:span_range ~parsing_diags ~parsing_feedback
        ~state:st ~parsing_time
    in
    Continue { state = st; last_tok; node }
  (* We can interpret the command now *)
  | Process ast -> (
    let lines = doc.contents.lines in
    let process_res, info = interp_and_info ~parsing_time ~st ast in
    let f = Coq_utils.to_range ~lines in
    let { Coq.Protect.E.r; feedback } = Coq.Protect.E.map_loc ~f process_res in
    match r with
    | Coq.Protect.R.Interrupted ->
      (* Exit *)
      Interrupted last_tok
    | Coq.Protect.R.Completed res ->
      let ast_loc = Coq.Ast.loc ast |> Option.get in
      let ast_range = Coq_utils.to_range ~lines ast_loc in
      (* The evaluation by Coq fully completed, then we can resume checking from
         this point then, hence the new last valid token last_tok_new *)
      let last_tok_new = Coq.Parsing.Parsable.loc doc_handle in
      let last_tok_new = Coq_utils.to_range ~lines last_tok_new in
      node_of_coq_result ~doc ~range:ast_range ~ast ~st ~parsing_diags
        ~parsing_feedback ~feedback ~info last_tok_new res)

module Target = struct
  type t =
    | End
    | Position of int * int

  let reached ~(range : Types.Range.t) (line, col) =
    let reached_line = range.end_.line in
    let reached_col = range.end_.character in
    line < reached_line || (line = reached_line && col <= reached_col)
end

let beyond_target (range : Types.Range.t) target =
  match target with
  | Target.End -> false
  | Position (cut_line, cut_col) -> Target.reached ~range (cut_line, cut_col)

let pr_target = function
  | Target.End -> "end"
  | Target.Position (l, c) -> Format.asprintf "{cutpoint l: %02d | c: %02d" l c

let log_beyond_target last_tok target =
  Io.Log.trace "beyond_target"
    ("target reached " ^ Types.Range.to_string last_tok);
  Io.Log.trace "beyond_target" ("target is " ^ pr_target target)

(* main interpretation loop *)
let process_and_parse ~ofmt ~target ~uri ~version doc last_tok doc_handle =
  let rec stm doc st (last_tok : Types.Range.t) =
    (* Reporting of progress and diagnostics (if dirty) *)
    let doc = send_eager_diagnostics ~ofmt ~uri ~version ~doc in
    report_progress ~ofmt ~doc last_tok;
    if Debug.parsing then Io.Log.trace "coq" "parsing sentence";
    if beyond_target last_tok target then
      let () = log_beyond_target last_tok target in
      (* We set to Completed.Yes when we have reached the EOI *)
      let completed =
        if last_tok.end_.offset >= doc.contents.last.offset then
          Completion.Yes last_tok
        else Completion.Stopped last_tok
      in
      set_completion ~completed doc
    else
      (* Parsing *)
      let lines = doc.contents.lines in
      let action, parsing_diags, parsing_feedback, parsing_time =
        parse_action ~lines ~st last_tok doc_handle
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
  | n :: _ ->
    Io.Log.trace "resume" ("last node :" ^ Types.Range.to_string n.range));
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
  let range = Completion.range completed in
  let status = Completion.to_string completed in
  Format.asprintf "done [%.2f]: document %s with pos %a" timestamp status
    Types.Range.pp range
  |> Io.Log.trace "check"

(* Rebuild a Coq loc from a range, this used to be done using [CLexer.after] but
   due to Fleche now being 100% based on unicode locations we implement our
   own *)
let loc_after ~lines ~uri (r : Types.Range.t) =
  let line_nb_last = r.end_.line + 1 in
  let end_index =
    let line = Array.get lines r.end_.line in
    if Debug.unicode then
      Io.Log.trace "loc_after"
        (Format.asprintf "str: '%s' | char: %d" line r.end_.character);
    Utf8.byte_of_char ~line ~char:r.end_.character
  in
  let bol_pos_last = r.end_.offset - end_index in
  { Loc.fname = init_fname ~uri
  ; line_nb = line_nb_last
  ; bol_pos = bol_pos_last
  ; line_nb_last
  ; bol_pos_last
  ; bp = r.end_.offset
  ; ep = r.end_.offset
  }

(** Setup parser and call the main routine *)
let resume_check ~ofmt ~(last_tok : Types.Range.t) ~doc ~target =
  let uri, version, contents = (doc.uri, doc.version, doc.contents) in
  (* Compute resume point, basically [CLexer.after] + stream setup *)
  let lines = doc.contents.lines in
  let resume_loc = loc_after ~lines ~uri last_tok in
  let offset = resume_loc.Loc.bp in
  let pcontent_len = contents.last.offset in
  match Util.safe_sub contents.text offset (pcontent_len - offset) with
  | None ->
    (* Guard against internal tricky eof errors *)
    let completed = Completion.Failed last_tok in
    set_completion ~completed doc
  | Some processed_content ->
    let handle =
      Coq.Parsing.Parsable.make ~loc:resume_loc
        Gramlib.Stream.(of_string ~offset processed_content)
    in
    process_and_parse ~ofmt ~target ~uri ~version doc last_tok handle

(** Check a document, if it was not completed already *)
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
