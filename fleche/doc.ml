(************************************************************************)
(* Flèche => document manager: Document                                 *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(* Should be moved to the right place *)
module Util = struct
  let hd_opt l =
    match l with
    | [] -> None
    | h :: _ -> Some h

  let rec last l =
    match l with
    | [] -> None
    | [ x ] -> Some x
    | _ :: xs -> last xs

  let build_span start_loc end_loc =
    Loc.
      { start_loc with
        line_nb_last = end_loc.line_nb_last
      ; bol_pos_last = end_loc.bol_pos_last
      ; ep = end_loc.ep
      }

  let print_stats () =
    (if !Config.v.mem_stats then
       let size = Memo.Interp.size () in
       Io.Log.trace "stats" (string_of_int size));
    let stats = Stats.dump () in
    Io.Log.trace "cache" (Stats.to_string stats);
    Io.Log.trace "cache" (Memo.CacheStats.stats ());
    (* this requires patches to Coq *)
    (* Io.Log.error "coq parsing" (CoqParsingStats.dump ()); *)
    (* CoqParsingStats.reset (); *)
    Memo.CacheStats.reset ();
    Stats.reset ()

  let safe_sub s pos len =
    if pos < 0 || len < 0 || pos > String.length s - len then (
      let s = String.sub s 0 (Stdlib.min 20 String.(length s - 1)) in
      Io.Log.trace "string_sub"
        (Format.asprintf "error for pos: %d len: %d str: %s" pos len s);
      None)
    else Some (String.sub s pos len)
end

module DDebug = struct
  let parsed_sentence ~ast =
    let loc = Coq.Ast.loc ast |> Option.get in
    let line = "[l: " ^ string_of_int (loc.Loc.line_nb - 1) ^ "] " in
    Io.Log.trace "coq"
      ("parsed sentence: " ^ line ^ Pp.string_of_ppcmds (Coq.Ast.print ast))

  let resume (last_tok : Lang.Range.t) version =
    Io.Log.trace "check"
      Format.(
        asprintf "resuming [v: %d], from: %d l: %d" version last_tok.end_.offset
          last_tok.end_.line)
end

(* [node list] is a very crude form of a meta-data map "loc -> data" , where for
   now [data] is only the goals. *)
module Node = struct
  module Ast = struct
    type t =
      { v : Coq.Ast.t
      ; ast_info : Lang.Ast.Info.t list option
      }

    let to_coq { v; _ } = Coq.Ast.to_coq v
  end

  module Info = struct
    type t =
      { cache_hit : bool
      ; parsing_time : float
      ; time : float option
      ; mw_prev : float
      ; mw_after : float
      ; stats : Stats.t  (** Info about cumulative stats *)
      }

    let make ?(cache_hit = false) ~parsing_time ?time ~mw_prev ~mw_after ~stats
        () =
      { cache_hit; parsing_time; time; mw_prev; mw_after; stats }

    let pp_time fmt = function
      | None -> Format.fprintf fmt "N/A"
      | Some time -> Format.fprintf fmt "%.3f" time

    let print { cache_hit; parsing_time; time; mw_prev; mw_after; stats } =
      let cptime = Stats.get_f stats ~kind:Stats.Kind.Parsing in
      let cetime = Stats.get_f stats ~kind:Stats.Kind.Exec in
      Format.asprintf
        "Cached: %b | P: %.3f / %.2f | E: %a / %.2f | M: %a | Diff: %a"
        cache_hit parsing_time cptime pp_time time cetime Stats.pp_words
        mw_after Stats.pp_words (mw_after -. mw_prev)
  end

  module Message = struct
    type t = Lang.Range.t option * int * Pp.t

    let feedback_to_message ~lines (loc, lvl, msg) =
      (Coq.Utils.to_orange ~lines loc, lvl, msg)
  end

  type t =
    { range : Lang.Range.t
    ; ast : Ast.t option  (** Ast of node *)
    ; state : Coq.State.t  (** (Full) State of node *)
    ; diags : Lang.Diagnostic.t list
    ; messages : Message.t list
    ; info : Info.t
    }

  let range { range; _ } = range
  let ast { ast; _ } = ast
  let state { state; _ } = state
  let diags { diags; _ } = diags
  let messages { messages; _ } = messages
  let info { info; _ } = info
  (* let with_state f n = Option.map (fun x -> (x, n.state)) (f n) *)
end

module Diags = struct
  let make ?extra range severity message =
    Lang.Diagnostic.{ range; severity; message; extra }

  (* ast-dependent error diagnostic generation *)
  let extra_diagnostics_of_ast ast =
    match (Node.Ast.to_coq ast).v with
    | Vernacexpr.
        { expr = VernacSynterp (VernacRequire (prefix, _export, module_refs))
        ; _
        } ->
      let refs = List.map fst module_refs in
      Some [ Lang.Diagnostic.Extra.FailedRequire { prefix; refs } ]
    | _ -> None

  let error ~range ~msg ~ast =
    let extra = extra_diagnostics_of_ast ast in
    make ?extra range 1 msg

  let of_feed ~drange (range, severity, message) =
    let range = Option.default drange range in
    make range severity message

  type partition_kind =
    | Left
    | Both
    | Right

  let partition ~f l =
    let rec part l r = function
      | [] -> (List.rev l, List.rev r)
      | x :: xs -> (
        match f x with
        | Left -> part (x :: l) r xs
        | Both -> part (x :: l) (x :: l) xs
        | Right -> part l (x :: r) xs)
    in
    part [] [] l

  let of_messages ~drange fbs =
    (* TODO, replace this by a cutoff level *)
    let cutoff =
      if !Config.v.show_coq_info_messages then 5
      else if !Config.v.show_notices_as_diagnostics then 4
      else 3
    in
    let f (_, lvl, _) =
      if lvl = 2 then Both else if lvl < cutoff then Left else Right
    in
    let diags, messages = partition ~f fbs in
    (List.map (of_feed ~drange) diags, messages)
end

module Completion = struct
  type t =
    | Yes of Lang.Range.t  (** Location of the last token in the document *)
    | Stopped of Lang.Range.t  (** Location of the last valid token *)
    | Failed of Lang.Range.t  (** Critical failure, like an anomaly *)
    | FailedPermanent of Lang.Range.t
        (** Temporal Coq hack, avoids any computation *)

  let range = function
    | Yes range | Stopped range | Failed range | FailedPermanent range -> range

  let to_string = function
    | Yes _ -> "fully checked"
    | Stopped _ -> "stopped"
    | Failed _ -> "failed"
    | FailedPermanent _ -> "refused to create due to Coq parsing bug"

  let is_completed = function
    | Yes _ | Failed _ | FailedPermanent _ -> true
    | _ -> false
end

(** Enviroment external to the document, this includes for now the [init] Coq
    state and the [workspace], which are used to build the first state of the
    document, usually by importing the prelude and other libs implicitly. *)
module Env = struct
  type t =
    { init : Coq.State.t
    ; workspace : Coq.Workspace.t
    }

  let make ~init ~workspace = { init; workspace }
end

(** A Flèche document is basically a [node list], which is a crude form of a
    meta-data map [Range.t -> data], where for now [data] is the contents of
    [Node.t]. *)
type t =
  { uri : Lang.LUri.File.t  (** [uri] of the document *)
  ; version : int  (** [version] of the document *)
  ; contents : Contents.t  (** [contents] of the document *)
  ; nodes : Node.t list  (** List of document nodes *)
  ; completed : Completion.t
        (** Status of the document, usually either completed, suspended, or
            waiting for some IO / external event *)
  ; toc : Lang.Range.t CString.Map.t  (** table of contents *)
  ; env : Env.t  (** External document enviroment *)
  ; root : Coq.State.t
        (** [root] contains the first state document state, obtained by applying
            a workspace to Coq's initial state *)
  ; diags_dirty : bool  (** internal field *)
  }

(* Flatten the list of document asts *)
let asts doc = List.filter_map Node.ast doc.nodes
let diags doc = List.concat_map (fun node -> node.Node.diags) doc.nodes

(* TOC handling *)
let rec add_toc_info toc { Lang.Ast.Info.name; range; children; _ } =
  let toc =
    match name.v with
    | None -> toc
    | Some id -> CString.Map.add id range toc
  in
  Option.cata (List.fold_left add_toc_info toc) toc children

let update_toc_info toc ast_info = List.fold_left add_toc_info toc ast_info

let update_toc_node toc node =
  match Node.ast node with
  | None -> toc
  | Some { Node.Ast.ast_info = None; _ } -> toc
  | Some { Node.Ast.ast_info = Some ast_info; _ } ->
    update_toc_info toc ast_info

let rebuild_toc nodes = List.fold_left update_toc_node CString.Map.empty nodes

let init_fname ~uri =
  let file = Lang.LUri.File.to_string_file uri in
  Loc.InFile { dirpath = None; file }

let init_loc ~uri = Loc.initial (init_fname ~uri)

(* default range for the node that contains the init feedback errors *)
let drange =
  let open Lang in
  let start = Point.{ line = 0; character = 0; offset = 0 } in
  let end_ = Point.{ line = 0; character = 1; offset = 1 } in
  Range.{ start; end_ }

let process_init_feedback ~lines ~stats state feedback =
  let messages = List.map (Node.Message.feedback_to_message ~lines) feedback in
  if not (CList.is_empty messages) then
    let diags, messages = Diags.of_messages ~drange messages in
    let parsing_time = 0.0 in
    let { Gc.major_words = mw_prev; _ } = Gc.quick_stat () in
    let info =
      Node.Info.make ~parsing_time ~mw_prev ~mw_after:mw_prev ~stats ()
    in
    let range = drange in
    [ { Node.range; ast = None; state; diags; messages; info } ]
  else []

(* Memoized call to [Coq.Init.doc_init] *)
let mk_doc ~env ~uri = Memo.Init.eval (env.Env.init, env.workspace, uri)

(* Create empty doc, in state [~completed] *)
let empty_doc ~uri ~contents ~version ~env ~root ~nodes ~completed =
  let lines = contents.Contents.lines in
  let init_loc = init_loc ~uri in
  let init_range = Coq.Utils.to_range ~lines init_loc in
  let toc = CString.Map.empty in
  let diags_dirty = not (CList.is_empty nodes) in
  let completed = completed init_range in
  { uri; contents; toc; version; env; root; nodes; diags_dirty; completed }

let error_doc ~loc ~message ~uri ~contents ~version ~env ~completed =
  let feedback = [ (loc, 1, Pp.str message) ] in
  let root = env.Env.init in
  let nodes = [] in
  (empty_doc ~uri ~version ~contents ~env ~root ~nodes ~completed, feedback)

let conv_error_doc ~raw ~uri ~version ~env ~root ~completed err =
  let contents = Contents.make_raw ~raw in
  let lines = contents.lines in
  let err = (None, 1, Pp.(str "Error in document conversion: " ++ str err)) in
  let stats = Stats.dump () in
  let nodes = process_init_feedback ~lines ~stats root [ err ] in
  empty_doc ~uri ~version ~env ~root ~nodes ~completed ~contents

let create ~env ~uri ~version ~contents =
  let () = Stats.reset () in
  let root = mk_doc ~env ~uri in
  Coq.Protect.E.map root ~f:(fun root ->
      let nodes = [] in
      let completed range = Completion.Stopped range in
      empty_doc ~uri ~contents ~version ~env ~root ~nodes ~completed)

(** Create a permanently failed doc, to be removed when we drop 8.16 support *)
let handle_failed_permanent ~env ~uri ~version ~contents =
  let completed range = Completion.FailedPermanent range in
  let loc, message = (None, "Document Failed Permanently due to Coq bugs") in
  let doc, feedback =
    error_doc ~loc ~message ~uri ~contents ~version ~env ~completed
  in
  let stats = Stats.dump () in
  let nodes =
    let lines = contents.Contents.lines in
    process_init_feedback ~lines ~stats env.Env.init feedback @ doc.nodes
  in
  let diags_dirty = not (CList.is_empty nodes) in
  { doc with nodes; diags_dirty }

(** Try to create a doc, if Coq execution fails, create a failed doc with the
    corresponding errors; for now we refine the contents step as to better setup
    the initial document. *)
let handle_doc_creation_exec ~env ~uri ~version ~contents =
  let completed range = Completion.Failed range in
  let { Coq.Protect.E.r; feedback } = create ~env ~uri ~version ~contents in
  let doc, extra_feedback =
    match r with
    | Interrupted ->
      let message = "Document Creation Interrupted!" in
      let loc = None in
      error_doc ~loc ~message ~uri ~version ~contents ~env ~completed
    | Completed (Error (User (loc, err_msg)))
    | Completed (Error (Anomaly (loc, err_msg))) ->
      let message =
        Format.asprintf "Doc.create, internal error: @[%a@]" Pp.pp_with err_msg
      in
      error_doc ~loc ~message ~uri ~version ~contents ~env ~completed
    | Completed (Ok doc) -> (doc, [])
  in
  let state = doc.root in
  let stats = Stats.dump () in
  let nodes =
    let lines = contents.Contents.lines in
    process_init_feedback ~lines ~stats state (feedback @ extra_feedback)
    @ doc.nodes
  in
  let diags_dirty = not (CList.is_empty nodes) in
  { doc with nodes; diags_dirty }

let handle_contents_creation ~env ~uri ~version ~raw ~completed f =
  match Contents.make ~uri ~raw with
  | Contents.R.Error err ->
    let root = env.Env.init in
    conv_error_doc ~raw ~uri ~version ~env ~root ~completed err
  | Contents.R.Ok contents -> f ~env ~uri ~version ~contents

let create ~env ~uri ~version ~raw =
  let completed range = Completion.Failed range in
  handle_contents_creation ~env ~uri ~version ~raw ~completed
    handle_doc_creation_exec

(* Used in bump, we should consolidate with create *)
let recreate ~doc ~version ~contents =
  let env, uri = (doc.env, doc.uri) in
  handle_doc_creation_exec ~env ~uri ~version ~contents

let create_failed_permanent ~env ~uri ~version ~raw =
  let completed range = Completion.FailedPermanent range in
  handle_contents_creation ~env ~uri ~version ~raw ~completed
    handle_failed_permanent

let recover_up_to_offset ~init_range doc offset =
  Io.Log.trace "prefix"
    (Format.asprintf "common prefix offset found at %d" offset);
  let rec find acc_nodes acc_range nodes =
    match nodes with
    | [] -> (List.rev acc_nodes, acc_range)
    | n :: ns ->
      if Debug.scan then
        Io.Log.trace "scan"
          (Format.asprintf "consider node at %a" Lang.Range.pp n.Node.range);
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
  let toc = rebuild_toc nodes in
  Io.Log.trace "prefix" ("resuming from " ^ Lang.Range.to_string range);
  let completed = Completion.Stopped range in
  (nodes, completed, toc)

let bump_version ~init_range ~version ~contents doc =
  (* When a new document, we resume checking from a common prefix *)
  let nodes, completed, toc = compute_common_prefix ~init_range ~contents doc in
  (* Important: uri, root remain the same *)
  let uri = doc.uri in
  let root = doc.root in
  let env = doc.env in
  { uri
  ; version
  ; root
  ; nodes
  ; contents
  ; toc
  ; diags_dirty = true (* EJGA: Is it worth to optimize this? *)
  ; completed
  ; env
  }

let bump_version ~version ~(contents : Contents.t) doc =
  let init_loc = init_loc ~uri:doc.uri in
  let init_range = Coq.Utils.to_range ~lines:contents.lines init_loc in
  match doc.completed with
  (* We can do better, but we need to handle the case where the anomaly is when
     restoring / executing the first sentence *)
  | FailedPermanent _ -> doc
  | Failed _ ->
    (* re-create the document on failed, as the env may have changed *)
    recreate ~doc ~version ~contents
  | Stopped _ | Yes _ -> bump_version ~init_range ~version ~contents doc

let bump_version ~version ~raw doc =
  let uri = doc.uri in
  match Contents.make ~uri ~raw with
  | Contents.R.Error e ->
    let completed range = Completion.Failed range in
    conv_error_doc ~raw ~uri ~version ~env:doc.env ~root:doc.root ~completed e
  | Contents.R.Ok contents -> bump_version ~version ~contents doc

let add_node ~node doc =
  let diags_dirty = if node.Node.diags <> [] then true else doc.diags_dirty in
  let toc = update_toc_node doc.toc node in
  { doc with nodes = node :: doc.nodes; toc; diags_dirty }

let send_eager_diagnostics ~io ~uri ~version ~doc =
  (* this is too noisy *)
  (* let proc_diag = mk_diag loc 3 (Pp.str "Processing") in *)
  (* Io.Report.diagnostics ~uri ~version (proc_diag :: doc.diags)); *)
  if doc.diags_dirty && !Config.v.eager_diagnostics then (
    let diags = diags doc in
    Io.Report.diagnostics ~io ~uri ~version diags;
    { doc with diags_dirty = false })
  else doc

let set_completion ~completed doc = { doc with completed }

(* We approximate the remnants of the document. It would be easier if instead of
   reporting what is missing, we would report what is done, but for now we are
   trying this paradigm.

   As we are quite dynamic (for now) in terms of what we observe of the document
   (basically we observe it linearly), we must compute the final position with a
   bit of a hack. *)
let compute_progress end_ (last_done : Lang.Range.t) =
  let start = last_done.end_ in
  let range = Lang.Range.{ start; end_ } in
  { Progress.Info.range; kind = 1 }

let report_progress ~io ~doc (last_tok : Lang.Range.t) =
  let progress = compute_progress doc.contents.last last_tok in
  Io.Report.fileProgress ~io ~uri:doc.uri ~version:doc.version [ progress ]

(* XXX: Save on close? *)
(* let close_doc _modname = () *)

let parse_stm ~st ps =
  let f ps = Coq.Parsing.parse ~st ps in
  Stats.record ~kind:Stats.Kind.Parsing ~f ps

module Recovery_context = struct
  type t =
    { contents : Contents.t
          (** Contents of the document (for syntax-based recovery) *)
    ; last_tok : Lang.Range.t  (** Position of the last token parsed *)
    ; nodes : Node.t list
          (** All nodes of the document (to be replaced by the structural
              solution *)
    ; ast : Coq.Ast.t option
          (** Ast of the sentence that failed, if available *)
    }

  let make ~contents ~last_tok ~nodes ?ast () =
    { contents; last_tok; nodes; ast }
end

(* This is not in its own module because we don't want to move the definition of
   [Node.t] out (yet) *)
module Recovery : sig
  val handle : context:Recovery_context.t -> st:Coq.State.t -> Coq.State.t
end = struct
  (* Returns node before / after, will be replaced by the right structure, we
     can also do dynamic by looking at proof state *)
  let rec find_proof_start nodes =
    match nodes with
    | [] -> None
    | { Node.ast = None; _ } :: ns -> find_proof_start ns
    | ({ ast = Some ast; _ } as n) :: ns -> (
      match (Node.Ast.to_coq ast).CAst.v.Vernacexpr.expr with
      | Vernacexpr.VernacSynPure (VernacStartTheoremProof _)
      | VernacSynPure (VernacDefinition (_, _, ProveBody _)) ->
        Some (n, Util.hd_opt ns)
      | _ -> find_proof_start ns)

  let recovery_for_failed_qed ~default nodes =
    match find_proof_start nodes with
    | None -> Coq.Protect.E.ok (default, None)
    | Some ({ range; state; _ }, prev) -> (
      if !Config.v.admit_on_bad_qed then
        Memo.Admit.eval state
        |> Coq.Protect.E.map ~f:(fun state -> (state, Some range))
      else
        match prev with
        | None -> Coq.Protect.E.ok (default, None)
        | Some { state; range; _ } -> Coq.Protect.E.ok (state, Some range))

  let log_qed_recovery v =
    Coq.Protect.E.map ~f:(fun (st, range) ->
        let loc_msg = Option.cata Lang.Range.to_string "no loc" range in
        Io.Log.trace "recovery"
          ("success" ^ loc_msg ^ " " ^ Memo.Interp.input_info (st, v));
        st)

  (* Contents-based recovery heuristic, special 'Qed.' case when `Qed.` is part
     of the error *)
  let extract_qed Lang.Range.{ end_; _ } { Contents.lines; _ } =
    let Lang.Point.{ line; character; _ } = end_ in
    let line = Array.get lines line in
    if character > 3 && String.length line > 3 then
      let coff = character - 4 in
      Some (String.init 3 (fun idx -> line.[idx + coff]))
    else None

  let lex_recovery_heuristic last_tok contents nodes st =
    match extract_qed last_tok contents with
    | Some txt when String.equal txt "Qed" ->
      Io.Log.trace "lex recovery" "qed detected";
      recovery_for_failed_qed ~default:st nodes |> Coq.Protect.E.map ~f:fst
    | Some _ | None -> Coq.Protect.E.ok st

  (* AST-based heuristics: Qed, bullets, ... *)
  let ast_recovery_heuristic last_tok contents nodes st v =
    match (Coq.Ast.to_coq v).CAst.v.Vernacexpr.expr with
    (* Drop the top proof state if we reach a faulty Qed. *)
    | Vernacexpr.VernacSynPure (VernacEndProof _) ->
      Io.Log.trace "recovery" "qed";
      recovery_for_failed_qed ~default:st nodes |> log_qed_recovery v
    (* If a new focus (or unfocusing) fails, admit the proof and try again *)
    | Vernacexpr.VernacSynPure (VernacBullet _ | Vernacexpr.VernacEndSubproof)
      ->
      Io.Log.trace "recovery" "bullet";
      Coq.State.admit_goal ~st
      |> Coq.Protect.E.bind ~f:(fun st -> Coq.Interp.interp ~st v)
    | _ ->
      (* Fallback to qed special lex case *)
      lex_recovery_heuristic last_tok contents nodes st

  (* XXX: This should be refined. *)
  let handle ~context ~st =
    let { Recovery_context.contents; last_tok; nodes; ast } = context in
    let { Coq.Protect.E.r; feedback = _ } =
      match ast with
      | None -> lex_recovery_heuristic last_tok contents nodes st
      | Some ast -> ast_recovery_heuristic last_tok contents nodes st ast
    in
    match r with
    | Interrupted -> st
    | Completed (Ok st) -> st
    | Completed (Error _) -> st
end

let interp_and_info ~parsing_time ~st ast =
  let { Gc.major_words = mw_prev; _ } = Gc.quick_stat () in
  (* memo memory stats are disabled: slow and misleading *)
  let { Memo.Stats.res; cache_hit; memory = _; time } =
    Memo.Interp.eval (st, ast)
  in
  let { Gc.major_words = mw_after; _ } = Gc.quick_stat () in
  let stats = Stats.dump () in
  let info =
    Node.Info.make ~cache_hit ~parsing_time ~time ~mw_prev ~mw_after ~stats ()
  in
  (res, info)

type parse_action =
  | EOF of Completion.t (* completed *)
  | Skip of
      Lang.Range.t
      * Lang.Range.t (* span of the skipped sentence + last valid token *)
  | Process of Coq.Ast.t (* success! *)

(* Returns parse_action, diags, parsing_time *)
let parse_action ~lines ~st last_tok doc_handle =
  let start_loc = Coq.Parsing.Parsable.loc doc_handle |> CLexer.after in
  let parse_res, time = parse_stm ~st doc_handle in
  let f = Coq.Utils.to_range ~lines in
  let { Coq.Protect.E.r; feedback } = Coq.Protect.E.map_loc ~f parse_res in
  match r with
  | Coq.Protect.R.Interrupted -> (EOF (Stopped last_tok), [], feedback, time)
  | Coq.Protect.R.Completed res -> (
    match res with
    | Ok None ->
      (* We actually need to fix Coq to return the location of the true file
         EOF, the below trick seems to work tho. Coq fix involves updating the
         type of `Pcoq.main_entry` *)
      let last_tok = Coq.Parsing.Parsable.loc doc_handle in
      let last_tok = Coq.Utils.to_range ~lines last_tok in
      (EOF (Yes last_tok), [], feedback, time)
    | Ok (Some ast) ->
      let () = if Debug.parsing then DDebug.parsed_sentence ~ast in
      (Process ast, [], feedback, time)
    | Error (Anomaly (_, msg)) | Error (User (None, msg)) ->
      (* We don't have a better alternative :(, usually missing error loc here
         means an anomaly, so we stop *)
      let err_range = last_tok in
      let parse_diags = [ Diags.make err_range 1 msg ] in
      (EOF (Failed last_tok), parse_diags, feedback, time)
    | Error (User (Some err_range, msg)) ->
      let parse_diags = [ Diags.make err_range 1 msg ] in
      Coq.Parsing.discard_to_dot doc_handle;
      let last_tok = Coq.Parsing.Parsable.loc doc_handle in
      let last_tok_range = Coq.Utils.to_range ~lines last_tok in
      let span_loc = Util.build_span start_loc last_tok in
      let span_range = Coq.Utils.to_range ~lines span_loc in
      (Skip (span_range, last_tok_range), parse_diags, feedback, time))

(* Result of node-building action *)
type document_action =
  | Stop of Completion.t * Node.t
  | Continue of
      { state : Coq.State.t
      ; last_tok : Lang.Range.t
      ; node : Node.t
      }
  | Interrupted of Lang.Range.t

let unparseable_node ~range ~parsing_diags ~parsing_feedback ~state
    ~parsing_time =
  let fb_diags, messages = Diags.of_messages ~drange:range parsing_feedback in
  let diags = fb_diags @ parsing_diags in
  let stats = Stats.dump () in
  let { Gc.major_words = mw_prev; _ } = Gc.quick_stat () in
  let info =
    Node.Info.make ~parsing_time ~mw_prev ~mw_after:mw_prev ~stats ()
  in
  { Node.range; ast = None; diags; messages; state; info }

let assemble_diags ~range ~parsing_diags ~parsing_feedback ~diags ~feedback =
  let parsing_fb_diags, parsing_messages =
    Diags.of_messages ~drange:range parsing_feedback
  in
  let fb_diags, fb_messages = Diags.of_messages ~drange:range feedback in
  let diags = parsing_diags @ parsing_fb_diags @ fb_diags @ diags in
  let messages = parsing_messages @ fb_messages in
  (diags, messages)

let parsed_node ~range ~ast ~state ~parsing_diags ~parsing_feedback ~diags
    ~feedback ~info =
  let diags, messages =
    assemble_diags ~range ~parsing_diags ~parsing_feedback ~diags ~feedback
  in
  { Node.range; ast = Some ast; diags; messages; state; info }

let strategy_of_coq_err ~node ~state ~last_tok = function
  | Coq.Protect.Error.Anomaly _ -> Stop (Failed last_tok, node)
  | User _ -> Continue { state; last_tok; node }

let node_of_coq_result ~doc ~range ~ast ~st ~parsing_diags ~parsing_feedback
    ~feedback ~info last_tok res =
  match res with
  | Ok state ->
    let node =
      parsed_node ~range ~ast ~state ~parsing_diags ~parsing_feedback ~diags:[]
        ~feedback ~info
    in
    Continue { state; last_tok; node }
  | Error (Coq.Protect.Error.Anomaly (err_range, msg) as coq_err)
  | Error (User (err_range, msg) as coq_err) ->
    let err_range = Option.default range err_range in
    let err_diags = [ Diags.error ~range:err_range ~msg ~ast ] in
    let contents, nodes = (doc.contents, doc.nodes) in
    let context =
      Recovery_context.make ~contents ~last_tok ~nodes ~ast:ast.v ()
    in
    let recovery_st = Recovery.handle ~context ~st in
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
    let context =
      Recovery_context.make ~contents:doc.contents ~last_tok ~nodes:doc.nodes ()
    in
    let st = Recovery.handle ~context ~st in
    let node =
      unparseable_node ~range:span_range ~parsing_diags ~parsing_feedback
        ~state:st ~parsing_time
    in
    Continue { state = st; last_tok; node }
  (* We can interpret the command now *)
  | Process ast -> (
    let lines = doc.contents.lines in
    let process_res, info = interp_and_info ~parsing_time ~st ast in
    let f = Coq.Utils.to_range ~lines in
    let { Coq.Protect.E.r; feedback } = Coq.Protect.E.map_loc ~f process_res in
    match r with
    | Coq.Protect.R.Interrupted ->
      (* Exit *)
      Interrupted last_tok
    | Coq.Protect.R.Completed res ->
      let ast_loc = Coq.Ast.loc ast |> Option.get in
      let ast_range = Coq.Utils.to_range ~lines ast_loc in
      let ast =
        Node.Ast.{ v = ast; ast_info = Coq.Ast.make_info ~lines ~st ast }
      in
      (* The evaluation by Coq fully completed, then we can resume checking from
         this point then, hence the new last valid token last_tok_new *)
      let last_tok_new = Coq.Parsing.Parsable.loc doc_handle in
      let last_tok_new = Coq.Utils.to_range ~lines last_tok_new in
      node_of_coq_result ~doc ~range:ast_range ~ast ~st ~parsing_diags
        ~parsing_feedback ~feedback ~info last_tok_new res)

module Target = struct
  type t =
    | End
    | Position of int * int

  let reached ~(range : Lang.Range.t) (line, col) =
    let reached_line = range.end_.line in
    let reached_col = range.end_.character in
    line < reached_line || (line = reached_line && col <= reached_col)
end

let beyond_target (range : Lang.Range.t) target =
  match target with
  | Target.End -> false
  | Position (cut_line, cut_col) -> Target.reached ~range (cut_line, cut_col)

let pr_target = function
  | Target.End -> "end"
  | Target.Position (l, c) -> Format.asprintf "{cutpoint l: %02d | c: %02d" l c

let log_beyond_target last_tok target =
  Io.Log.trace "beyond_target"
    ("target reached " ^ Lang.Range.to_string last_tok);
  Io.Log.trace "beyond_target" ("target is " ^ pr_target target)

let max_errors_node ~state ~range =
  let msg = Pp.str "Maximum number of errors reached" in
  let parsing_diags = [ Diags.make range 1 msg ] in
  unparseable_node ~range ~parsing_diags ~parsing_feedback:[] ~state
    ~parsing_time:0.0

(* main interpretation loop *)
let process_and_parse ~io ~target ~uri ~version doc last_tok doc_handle =
  let rec stm doc st (last_tok : Lang.Range.t) acc_errors =
    (* Reporting of progress and diagnostics (if dirty) *)
    let doc = send_eager_diagnostics ~io ~uri ~version ~doc in
    report_progress ~io ~doc last_tok;
    if Debug.parsing then Io.Log.trace "coq" "parsing sentence";
    if acc_errors > !Config.v.max_errors then
      let completed = Completion.Failed last_tok in
      let node = max_errors_node ~state:st ~range:last_tok in
      let doc = add_node ~node doc in
      set_completion ~completed doc
    else if beyond_target last_tok target then
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
        (* See #445 *)
        report_progress ~io ~doc (Completion.range completed);
        set_completion ~completed doc
      | Continue { state; last_tok; node } ->
        let n_errors = CList.count Lang.Diagnostic.is_error node.Node.diags in
        let doc = add_node ~node doc in
        stm doc state last_tok (acc_errors + n_errors)
  in
  (* Reporting of progress and diagnostics (if stopped or failed, if completed
     the doc manager will take care of it) *)
  let doc =
    if not (Completion.is_completed doc.completed) then
      let () = report_progress ~io ~doc last_tok in
      send_eager_diagnostics ~io ~uri ~version ~doc
    else doc
  in
  (* Set the document to "internal" mode, stm expects the node list to be in
     reversed order *)
  let doc = { doc with nodes = List.rev doc.nodes } in
  (* Note that nodes and diags are in reversed order here *)
  (match doc.nodes with
  | [] -> ()
  | n :: _ ->
    Io.Log.trace "resume" ("last node :" ^ Lang.Range.to_string n.range));
  let last_node = Util.hd_opt doc.nodes in
  let st, stats =
    Option.cata
      (fun { Node.state; info = { stats; _ }; _ } -> (state, stats))
      (doc.root, Stats.zero ())
      last_node
  in
  Stats.restore stats;
  let doc = stm doc st last_tok 0 in
  (* Set the document to "finished" mode: reverse the node list *)
  let doc = { doc with nodes = List.rev doc.nodes } in
  doc

let log_doc_completion (completed : Completion.t) =
  let timestamp = Unix.gettimeofday () in
  let range = Completion.range completed in
  let status = Completion.to_string completed in
  Format.asprintf "done [%.2f]: document %s with pos %a" timestamp status
    Lang.Range.pp range
  |> Io.Log.trace "check"

(* Rebuild a Coq loc from a range, this used to be done using [CLexer.after] but
   due to Fleche now being 100% based on unicode locations we implement our
   own *)
let debug_loc_after line (r : Lang.Range.t) =
  if Debug.unicode then
    Io.Log.trace "loc_after"
      (Format.asprintf "str: '%s' | char: %d" line r.end_.character)

let loc_after ~lines ~uri (r : Lang.Range.t) =
  let line_nb_last = r.end_.line + 1 in
  let end_index =
    let line = Array.get lines r.end_.line in
    debug_loc_after line r;
    match Coq.Utf8.index_of_char ~line ~char:r.end_.character with
    | None -> String.length line
    | Some index -> index
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
let resume_check ~io ~(last_tok : Lang.Range.t) ~doc ~target =
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
    process_and_parse ~io ~target ~uri ~version doc last_tok handle

(** Check a document, if it was not completed already *)
let check ~io ~target ~doc () =
  match doc.completed with
  | Yes _ ->
    Io.Log.trace "check" "resuming, completed=yes, nothing to do";
    doc
  | FailedPermanent _ | Failed _ ->
    Io.Log.trace "check" "can't resume, failed=yes, nothing to do";
    doc
  | Stopped last_tok ->
    DDebug.resume last_tok doc.version;
    let doc = resume_check ~io ~last_tok ~doc ~target in
    log_doc_completion doc.completed;
    Util.print_stats ();
    doc

let save ~doc =
  match doc.completed with
  | Yes _ ->
    let st = Util.last doc.nodes |> Option.cata Node.state doc.root in
    let uri = doc.uri in
    let ldir = Coq.Workspace.dirpath_of_uri ~uri in
    let in_file = Lang.LUri.File.to_string_file uri in
    Coq.State.in_stateM ~st
      ~f:(fun () -> Coq.Save.save_vo ~st ~ldir ~in_file)
      ()
  | _ ->
    let error = Pp.(str "Can't save document that failed to check") in
    let r = Coq.Protect.R.error error in
    Coq.Protect.E.{ r; feedback = [] }
