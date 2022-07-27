(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2022 Inria           -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

open Lsp_util
module LSP = Lsp.Base

type node =
  { ast : Coq_ast.t
  ; goal : Pp.t option
  }

(* Private. A doc is a list of nodes for now. The first element in the list is
   assumed to be the tip of the document. The initial document is the empty
   list. *)
type t =
  { uri : string
  ; version : int
  ; contents : string
  ; root : Coq_state.t
  ; nodes : node list
  }

(* let mk_error ~doc pos msg =
 *   LSP.mk_diagnostics ~uri:doc.uri ~version:doc.version [pos, 1, msg, None] *)

let mk_doc state =
  let root_state, vo_load_path, ml_include_path, _ = state in
  let libname = Names.(DirPath.make [ Id.of_string "foo" ]) in
  let require_libs = [ ("Coq.Init.Prelude", None, Some (Lib.Import, None)) ] in
  Coq_init.doc_init ~root_state ~vo_load_path ~ml_include_path ~libname
    ~require_libs

let create ~state ~uri ~version ~contents =
  { uri; contents; version; root = mk_doc state; nodes = [] }

(* XXX: Save on close? *)
(* let close_doc _modname = () *)

let parse_stm ~st ps =
  let mode = Coq_state.mode ~st in
  let st = Coq_state.parsing ~st in
  let parse ps =
    (* Coq is missing this, so we add it here. Note that this MUST run inside
       coq_protect *)
    Control.check_for_interrupt ();
    Vernacstate.Parser.parse st Pvernac.(main_entry mode) ps
    |> Option.map Coq_ast.of_coq
  in
  Stats.record ~kind:Stats.Kind.Parsing ~f:(Coq_protect.eval ~f:parse) ps

(* Read the input stream until a dot is encountered *)
let parse_to_dot : unit Pcoq.Entry.t =
  (* type 'a parser_fun = { parser_fun : te LStream.t -> 'a } *)
  let rec dot st =
    match Gramlib.LStream.next st with
    | Tok.KEYWORD ("." | "...") -> ()
    | Tok.EOI -> ()
    | _ -> dot st
  in
  Pcoq.Entry.of_parser "Coqtoplevel.dot" { parser_fun = dot }

(* If an error occurred while parsing, we try to read the input until a dot
   token is encountered. We assume that when a lexer error occurs, at least one
   char was eaten *)

let rec discard_to_dot ps =
  try Pcoq.Entry.parse parse_to_dot ps with
  | CLexer.Error.E _ -> discard_to_dot ps
  | e when CErrors.noncritical e -> ()

(* Gross hack *)
let proof_st = ref None

let register_hack_proof_recover ast st =
  match (Coq_ast.to_coq ast).CAst.v.Vernacexpr.expr with
  | Vernacexpr.VernacStartTheoremProof _ ->
    proof_st := Some st;
    ()
  | _ -> ()

(* Simple heuristic for Qed. *)
let state_recovery_heuristic st v =
  match (Coq_ast.to_coq v).CAst.v.Vernacexpr.expr with
  (* Drop the top proof state if we reach a faulty Qed. *)
  | Vernacexpr.VernacEndProof _ ->
    let st = Option.default st !proof_st in
    Lsp.Io.log_error "recovery" (Memo.input_info (v, st));
    proof_st := None;
    Coq_state.drop_proofs ~st
  | _ -> st

type process_action =
  | EOF
  | Skip
  | Process of Coq_ast.t

let json_of_diags ~uri ~version diags =
  LSP.mk_diagnostics ~uri ~version
  @@ List.fold_left
       (fun acc (pos, lvl, msg, goal) ->
         match pos with
         | None -> acc
         | Some pos -> (pos, lvl, msg, goal) :: acc)
       [] diags

(* Make each fb a diag *)
let process_feedback ~loc fbs =
  let fb_msg =
    Format.asprintf "feedbacks: %d @\n @[<v>%a@]"
      List.(length fbs)
      Format.(pp_print_list Pp.pp_with)
      fbs
  in
  [ (to_orange loc, 3, fb_msg, None) ]

(* XXX: Imperative problem *)
let process_and_parse ~ofmt ~uri ~version ~fb_queue doc =
  let loc = Loc.initial (InFile { dirpath = None; file = uri }) in
  let doc_handle =
    Pcoq.Parsable.make ~loc Gramlib.Stream.(of_string doc.contents)
  in
  let rec stm doc st diags =
    (* Eager update! *)
    (if Config.eager_diagnostics then
     let diags = json_of_diags ~uri ~version diags in
     Lsp.Io.send_json ofmt diags);
    (* if Lsp.Debug.parsing then Lsp.Io.log_error "coq" "parsing sentence"; *)
    (* Parsing *)
    let action, diags, parsing_time =
      match parse_stm ~st doc_handle with
      | Coq_protect.R.Interrupted, time -> (EOF, diags, time)
      | Coq_protect.R.Completed res, time -> (
        match res with
        | Ok None -> (EOF, diags, time)
        | Ok (Some ast) -> (Process ast, diags, time)
        | Error (loc, msg) ->
          let diags = (to_orange loc, 1, to_msg msg, None) :: diags in
          discard_to_dot doc_handle;
          (Skip, diags, time))
    in
    (* Execution *)
    match action with
    (* End of file *)
    | EOF -> (doc, st, diags)
    | Skip -> stm doc st diags
    (* We interpret the command now *)
    | Process ast -> (
      let loc = Coq_ast.loc ast in
      (if Lsp.Debug.parsing then
       let line =
         Option.cata
           (fun loc -> "[l: " ^ string_of_int loc.Loc.line_nb ^ "] ")
           "" loc
       in
       Lsp.Io.log_error "coq"
         ("parsed sentence: " ^ line ^ Pp.string_of_ppcmds (Coq_ast.print ast)));
      register_hack_proof_recover ast st;
      (* memory is disabled as it is quite slow and misleading *)
      let { Memo.Stats.res; cache_hit; memory = _; time } =
        Memo.interp_command ~st ~fb_queue ast
      in
      let cptime = Stats.get ~kind:Stats.Kind.Parsing in
      let memo_msg =
        Format.asprintf
          "Cache Hit: %b | Exec Time: %f | Parsing time: %f | Cumulative \
           parsing: %f"
          cache_hit time parsing_time cptime
      in
      let memo_diag = (to_orange loc, 4, memo_msg, None) in
      let diags = memo_diag :: diags in
      match res with
      | Coq_protect.R.Interrupted ->
        (* Exit *)
        (doc, st, diags)
      | Coq_protect.R.Completed res -> (
        match res with
        | Ok { res = st; goal; feedback } ->
          let ok_diag = (to_orange loc, 3, "OK", None) in
          let diags = ok_diag :: diags in
          let fb_diags = process_feedback ~loc feedback in
          let diags = fb_diags @ diags in
          let node = { ast; goal } in
          let doc = { doc with nodes = node :: doc.nodes } in
          stm doc st diags
        | Error (err_loc, msg) ->
          let loc = Option.append err_loc loc in
          let diags = (to_orange loc, 1, to_msg msg, None) :: diags in
          let node = { ast; goal = None } in
          (* This should be handled by Coq_protect.eval XXX *)
          fb_queue := [];
          let doc = { doc with nodes = node :: doc.nodes } in
          let st = state_recovery_heuristic st ast in
          stm doc st diags))
  in
  (* we re-start from the root *)
  stm doc doc.root []

let print_stats () =
  (if Config.mem_stats then
   let size = Memo.mem_stats () in
   Lsp.Io.log_error "stats" (string_of_int size));

  Lsp.Io.log_error "cache" (Stats.dump ());
  Lsp.Io.log_error "cache" (Memo.CacheStats.stats ());
  Lsp.Io.log_error "coq parsing" (Cstats.dump ());
  Cstats.reset ();
  Memo.CacheStats.reset ();
  Stats.reset ()

let check ~ofmt ~doc ~fb_queue =
  let uri, version = (doc.uri, doc.version) in

  (* Start library *)
  let doc, st, diags = (process_and_parse ~ofmt ~uri ~version ~fb_queue) doc in
  let doc = { doc with nodes = List.rev doc.nodes } in
  print_stats ();
  (doc, st, json_of_diags ~uri ~version diags)
