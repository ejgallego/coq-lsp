(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

module F = Format
module J = Yojson.Basic
module U = Yojson.Basic.Util

let    int_field name dict = U.to_int    List.(assoc name dict)
let   dict_field name dict = U.to_assoc  List.(assoc name dict)
let   list_field name dict = U.to_list   List.(assoc name dict)
let string_field name dict = U.to_string List.(assoc name dict)

(* Conditionals *)
let option_empty x = match x with | None -> true | Some _ -> false
let option_cata f x d = match x with | None -> d | Some x -> f x
let option_default x d = match x with | None -> d | Some x -> x

let oint_field  name dict = option_cata U.to_int List.(assoc_opt name dict) 0
let odict_field name dict = option_default U.(to_option to_assoc (option_default List.(assoc_opt name dict) `Null)) []

module LIO = Lsp.Io
module LSP = Lsp.Base

(* Request Handling: The client expects a reply *)
let do_initialize ofmt ~id _params =
  let msg = LSP.mk_reply ~id ~result:(
      `Assoc ["capabilities",
       `Assoc [
          "textDocumentSync", `Int 1
        ; "documentSymbolProvider", `Bool true
        ; "hoverProvider", `Bool true
        ; "completionProvider", `Assoc []
        ; "codeActionProvider", `Bool false
        ]]) in
  LIO.send_json ofmt msg

let do_shutdown ofmt ~id =
  let msg = LSP.mk_reply ~id ~result:`Null in
  LIO.send_json ofmt msg

let doc_table : (string, _) Hashtbl.t = Hashtbl.create 39
let completed_table : (string, Coq_doc.t * Vernacstate.t) Hashtbl.t = Hashtbl.create 39

(* Notification handling; reply is optional / asynchronous *)
let do_check_text ofmt ~state ~doc =
  let _, _, _, coq_queue = state in
  let doc, final_st, diags = Coq_doc.check ~doc ~coq_queue in
  Hashtbl.replace completed_table doc.uri (doc,final_st);
  LIO.send_json ofmt @@ diags

let do_change ofmt ~doc change =
  let open Coq_doc in
  LIO.log_error "checking file" (doc.uri ^ " / version: " ^ (string_of_int doc.version));
  let doc = { doc with contents = string_field "text" change; } in
  do_check_text ofmt ~doc

let do_open ofmt ~state params =
  let document = dict_field "textDocument" params in
  let uri, version, contents =
    string_field "uri" document,
    int_field "version" document,
    string_field "text" document in
  let doc = Coq_doc.create ~state ~uri ~contents ~version in
  begin match Hashtbl.find_opt doc_table uri with
    | None -> ()
    | Some _ -> LIO.log_error "do_open" ("file " ^ uri ^ " not properly closed by client")
  end;
  Hashtbl.add doc_table uri doc;
  do_check_text ofmt ~state ~doc

let do_change ofmt ~state params =
  let document = dict_field "textDocument" params in
  let uri, version  =
    string_field "uri" document,
    int_field "version" document in
  let changes = List.map U.to_assoc @@ list_field "contentChanges" params in
  let doc = Hashtbl.find doc_table uri in
  let doc = { doc with Coq_doc.version; } in
  List.iter (do_change ofmt ~state ~doc) changes

let do_close _ofmt params =
  let document = dict_field "textDocument" params in
  let doc_file = string_field "uri" document in
  Hashtbl.remove doc_table doc_file

let grab_doc params =
  let document = dict_field "textDocument" params in
  let doc_file = string_field "uri" document in
  let start_doc, end_doc = Hashtbl.(find doc_table doc_file, find completed_table doc_file) in
  doc_file, start_doc, end_doc

let mk_syminfo file (name, _path, kind, pos) : J.t =
  `Assoc [
    "name", `String name;
    "kind", `Int kind;            (* function *)
    "location", `Assoc [
      "uri", `String file
    ; "range", LSP.mk_range Lsp_util.(to_range pos)
    ]
  ]

let kind_of_type _tm = 13
(*
  let open Terms in
  let open Timed in
  let is_undef = option_empty !(tm.sym_def) && List.length !(tm.sym_rules) = 0 in
  match !(tm.sym_type) with
  | Vari _ ->
    13                         (* Variable *)
  | Type | Kind | Symb _ | _ when is_undef ->
    14                         (* Constant *)
  | _ ->
    12                         (* Function *)
*)

let match_coq_def f { Coq_doc.ast = v ; _ } =
  let open Vernacexpr in
  let ndecls =
    (* TODO: (co)fixpoint, instance, assumption *)
    match v.v.expr with
    | VernacDefinition (_, (CAst.{ loc = Some loc; v=name },_), _) ->
      Nameops.Name.fold_left (fun _ id -> [loc,id]) [] name
    | VernacStartTheoremProof (_, ndecls) ->
      let f_id = function
        | ((CAst.{ loc = None; _ },_),_) -> None
        | ((CAst.{ loc = Some loc; v },_),_) -> Some (loc, v)
      in
      CList.map_filter f_id ndecls
    | _ -> []
  in
  CList.map (fun (loc,id) -> f loc id) ndecls
(*
  | VernacLoad (_, _) -> (??)
  | VernacSyntaxExtension (_, _) -> (??)
  | VernacOpenCloseScope (_, _) -> (??)
  | VernacDeclareScope _ -> (??)
  | VernacDelimiters (_, _) -> (??)
  | VernacBindScope (_, _) -> (??)
  | VernacInfix (_, _, _) -> (??)
  | VernacNotation (_, _, _) -> (??)
  | VernacNotationAddFormat (_, _, _) -> (??)
  | VernacDeclareCustomEntry _ -> (??)
  | VernacEndProof _ -> (??)
  | VernacExactProof _ -> (??)
  | VernacAssumption (_, _, _) -> (??)
  | VernacInductive (_, _, _, _) -> (??)
  | VernacFixpoint (_, _) -> (??)
  | VernacCoFixpoint (_, _) -> (??)
  | VernacScheme _ -> (??)
  | VernacCombinedScheme (_, _) -> (??)
  | VernacUniverse _ -> (??)
  | VernacConstraint _ -> (??)
  | VernacBeginSection _ -> (??)
  | VernacEndSegment _ -> (??)
  | VernacRequire (_, _, _) -> (??)
  | VernacImport (_, _) -> (??)
  | VernacCanonical _ -> (??)
  | VernacCoercion (_, _, _) -> (??)
  | VernacIdentityCoercion (_, _, _) -> (??)
  | VernacNameSectionHypSet (_, _) -> (??)
  | VernacInstance (_, _, _, _) -> (??)
  | VernacDeclareInstance (_, _, _) -> (??)
  | VernacContext _ -> (??)
  | VernacExistingInstance _ -> (??)
  | VernacExistingClass _ -> (??)
  | VernacDeclareModule (_, _, _, _) -> (??)
  | VernacDefineModule (_, _, _, _, _) -> (??)
  | VernacDeclareModuleType (_, _, _, _) -> (??)
  | VernacInclude _ -> (??)
  | VernacSolveExistential (_, _) -> (??)
  | VernacAddLoadPath (_, _, _) -> (??)
  | VernacRemoveLoadPath _ -> (??)
  | VernacAddMLPath (_, _) -> (??)
  | VernacDeclareMLModule _ -> (??)
  | VernacChdir _ -> (??)
  | VernacWriteState _ -> (??)
  | VernacRestoreState _ -> (??)
  | VernacResetName _ -> (??)
  | VernacResetInitial -> (??)
  | VernacBack _ -> (??)
  | VernacBackTo _ -> (??)
  | VernacCreateHintDb (_, _) -> (??)
  | VernacRemoveHints (_, _) -> (??)
  | VernacHints (_, _) -> (??)
  | VernacSyntacticDefinition (_, _, _) -> (??)
  | VernacArguments (_, _, _, _, _) -> (??)
  | VernacReserve _ -> (??)
  | VernacGeneralizable _ -> (??)
  | VernacSetOpacity _ -> (??)
  | VernacSetStrategy _ -> (??)
  | VernacUnsetOption (_, _) -> (??)
  | VernacSetOption (_, _, _) -> (??)
  | VernacAddOption (_, _) -> (??)
  | VernacRemoveOption (_, _) -> (??)
  | VernacMemOption (_, _) -> (??)
  | VernacPrintOption _ -> (??)
  | VernacCheckMayEval (_, _, _) -> (??)
  | VernacGlobalCheck _ -> (??)
  | VernacDeclareReduction (_, _) -> (??)
  | VernacPrint _ -> (??)
  | VernacSearch (_, _, _) -> (??)
  | VernacLocate _ -> (??)
  | VernacRegister (_, _) -> (??)
  | VernacPrimitive (_, _, _) -> (??)
  | VernacComments _ -> (??)
  | VernacAbort _ -> (??)
  | VernacAbortAll -> (??)
  | VernacRestart -> (??)
  | VernacUndo _ -> (??)
  | VernacUndoTo _ -> (??)
  | VernacFocus _ -> (??)
  | VernacUnfocus -> (??)
  | VernacUnfocused -> (??)
  | VernacBullet _ -> (??)
  | VernacSubproof _ -> (??)
  | VernacEndSubproof -> (??)
  | VernacShow _ -> (??)
  | VernacCheckGuard -> (??)
  | VernacProof (_, _) -> (??)
  | VernacProofMode _ -> (??)
  | VernacExtend (_, _) -> (??))
*)

let grab_definitions f nodes =
  List.fold_left
    (fun acc s -> match_coq_def f s @ acc)
    [] nodes

let do_symbols ofmt ~id params =
  let file, _, (doc,_) = grab_doc params in
  let f loc id = mk_syminfo file (Names.Id.to_string id, "", 12, loc) in
  let slist = grab_definitions f doc.Coq_doc.nodes in
  let msg = LSP.mk_reply ~id ~result:(`List slist) in
  LIO.send_json ofmt msg

let get_docTextPosition params =
  let document = dict_field "textDocument" params in
  let file = string_field "uri" document in
  let pos = dict_field "position" params in
  let line, character = int_field "line" pos, int_field "character" pos in
  file, line, character

(* XXX refactor *)
let in_range ?loc (line, pos) =
  match loc with
  | None -> false
  | Some loc ->
    let Loc.{line_nb=line1; line_nb_last=line2; bol_pos; bol_pos_last; bp; ep; _} = loc in
    let col1 = bp - bol_pos in
    let col2 = ep - bol_pos_last in
    line1 - 1 < line && line < line2 -1 ||
    (line1 - 1 = line && col1 <= pos) ||
    (line2 - 1 = line && pos <= col2)

let get_goals ~doc ~line ~pos =
  let node =
    List.find_opt (fun { Coq_doc.ast = CAst.{ loc ; _ } ; _} ->
        in_range ?loc (line,pos)) doc.Coq_doc.nodes
  in
  Option.map (fun node ->
      Option.cata Pp.string_of_ppcmds "No goals" node.Coq_doc.goal) node

let do_hover ofmt ~id params =
  let uri, line, pos = get_docTextPosition params in
  let doc, _ = Hashtbl.find completed_table uri in
  (get_goals ~doc ~line ~pos) |>
  Option.iter (fun goals ->
    let result = `Assoc [ "contents", `String goals] in
    let msg = LSP.mk_reply ~id ~result in
    LIO.send_json ofmt msg)

let do_completion ofmt ~id params =
  let uri, _line, _pos = get_docTextPosition params in
  let doc, _ = Hashtbl.find completed_table uri in
  let f _loc id = `Assoc [ "label", `String Names.Id.(to_string id) ] in
  let clist = grab_definitions f doc.Coq_doc.nodes in
  let result = `List clist in
  let msg = LSP.mk_reply ~id ~result in
  LIO.send_json ofmt msg
  (* LIO.log_error "do_completion" (string_of_int line ^"-"^ string_of_int pos) *)

(* XXX: We could split requests and notifications but with the OCaml
   theading model there is not a lot of difference yet; something to
   think for the future. *)
let dispatch_message ofmt ~state dict =
  let id     = oint_field "id" dict in
  let params = odict_field "params" dict in
  match string_field "method" dict with
  (* Requests *)
  | "initialize" ->
    do_initialize ofmt ~id params
  | "shutdown" ->
    do_shutdown ofmt ~id

  (* Symbols in the document *)
  | "textDocument/completion" ->
    do_completion ofmt ~id params

  | "textDocument/documentSymbol" ->
    do_symbols ofmt ~id params

  | "textDocument/hover" ->
    do_hover ofmt ~id params

  (* Notifications *)
  | "textDocument/didOpen" ->
    do_open ofmt ~state params

  | "textDocument/didChange" ->
    do_change ofmt ~state params

  | "textDocument/didClose" ->
    do_close ofmt params

  | "exit" ->
    exit 0

  (* NOOPs *)
  | "initialized"
  | "workspace/didChangeWatchedFiles" ->
    ()
  | msg ->
    LIO.log_error "no_handler" msg

let process_input ofmt ~state (com : J.t) =
  try dispatch_message ofmt ~state (U.to_assoc com)
  with
  | U.Type_error (msg, obj) ->
    LIO.log_object msg obj
  | exn ->
    let bt = Printexc.get_backtrace () in
    LIO.log_error "process_input" (Printexc.to_string exn);
    LIO.log_error "process_input" Pp.(string_of_ppcmds CErrors.(iprint (Exninfo.capture exn)));
    LIO.log_error "BT" bt

let lsp_main log_file std vo_load_path ml_include_path =

  Printexc.record_backtrace true;
  LSP.std_protocol := std;

  let oc = F.std_formatter in

  let debug_oc = open_out log_file in
  LIO.debug_fmt := F.formatter_of_out_channel debug_oc;

  (* XXX: Capture better / per sentence. *)
  let lp_oc = open_out "log-coq_lsp.txt" in
  let lp_fmt = F.formatter_of_out_channel lp_oc in

  (* Dedukti stuff *)
  (* Console.out_fmt := lp_fmt;
   * Console.err_fmt := lp_fmt; *)
  (* Console.verbose := 4; *)

  let fb_handler, fb_queue =
    let q = Queue.create () in
    (fun Feedback.{ contents; _ } ->
       Format.fprintf lp_fmt "%s@\n%!" "fb received";
       match contents with
       | Message(_lvl,_loc,msg)-> Queue.push Pp.(string_of_ppcmds msg) q
       | _ -> ()
    ), q
  in
  let state =
    Coq_init.coq_init
      Coq_init.{ fb_handler
               ; ml_load = None
               ; debug = false
               },
    vo_load_path,
    ml_include_path,
    fb_queue
  in

  let rec loop state =
    let com = LIO.read_request stdin in
    LIO.log_object "read" com;
    process_input oc ~state com;
    F.pp_print_flush lp_fmt (); flush lp_oc;
    loop state
  in
  try loop state
  with exn ->
    let bt = Printexc.get_backtrace () in
    LIO.log_error "fatal error" Printexc.(to_string exn);
    LIO.log_error "fatal_error" Pp.(string_of_ppcmds CErrors.(iprint (Exninfo.capture exn)));
    LIO.log_error "BT" bt;
    F.pp_print_flush !LIO.debug_fmt ();
    flush_all ();
    close_out debug_oc;
    close_out lp_oc

(* Arguments handling *)
open Cmdliner

(* let bt =
 *   let doc = "Enable backtraces" in
 *   Arg.(value & flag & info ["bt"] ~doc) *)

let log_file =
  let doc = "Log to $(docv)" in
  Arg.(value & opt string "log-lsp.txt" & info ["log_file"] ~docv:"FILE" ~doc)

let std =
  let doc = "Restrict to standard LSP protocol" in
  Arg.(value & flag & info ["std"] ~doc)

let coq_lp_conv ~implicit (unix_path,lp) =
  { Loadpath.coq_path  = Libnames.dirpath_of_string lp
  ; unix_path
  ; has_ml = true
  ; implicit
  ; recursive = true
  }

let coqlib =
  let doc = "Load Coq.Init.Prelude from $(docv); plugins/ and theories/ should live there." in
  Arg.(value & opt string Coq_config.coqlib & info ["coqlib"] ~docv:"COQPATH" ~doc)

let rload_path : Loadpath.vo_path list Term.t =
  let doc = "Bind a logical loadpath LP to a directory DIR and implicitly open its namespace." in
  Term.(const List.(map (coq_lp_conv ~implicit:true)) $
        Arg.(value & opt_all (pair dir string) [] & info ["R"; "rec-load-path"] ~docv:"DIR,LP"~doc))

let load_path : Loadpath.vo_path list Term.t =
  let doc = "Bind a logical loadpath LP to a directory DIR" in
  Term.(const List.(map (coq_lp_conv ~implicit:false)) $
        Arg.(value & opt_all (pair dir string) [] & info ["Q"; "load-path"] ~docv:"DIR,LP" ~doc))

let ml_include_path : string list Term.t =
  let doc = "Include DIR in default loadpath, for locating ML files" in
  Arg.(value & opt_all dir [] & info ["I"; "ml-include-path"] ~docv:"DIR" ~doc)

let coq_loadpath_default ~implicit coq_path =
  let mk_path prefix = coq_path ^ "/" ^ prefix in
  let mk_lp ~ml ~root ~dir ~implicit =
    { Loadpath.unix_path = mk_path dir
    ; coq_path  = root
    ; has_ml    = ml
    ; implicit
    ; recursive = true }
  in
  let coq_root     = Names.DirPath.make [Libnames.coq_root] in
  let default_root = Libnames.default_root_prefix in
  [mk_lp ~ml:true ~root:coq_root     ~implicit       ~dir:"../coq-core/plugins";
   mk_lp ~ml:false ~root:coq_root    ~implicit       ~dir:"theories";
   mk_lp ~ml:true ~root:default_root ~implicit:false ~dir:"user-contrib";
  ]

let term_append l = Term.(List.(fold_right (fun t l -> pure append $ t $ l) l (pure [])))

let lsp_cmd =
  let doc = "Coq LSP Server" in
  let man = [
    `S "DESCRIPTION";
    `P "Experimental Coq LSP server";
    `S "USAGE";
    `P "See the documentation on the project's webpage for more information"
  ]
  in
  let coq_loadpath = Term.(pure (coq_loadpath_default ~implicit:true) $ coqlib) in
  let vo_load_path = term_append [coq_loadpath; rload_path; load_path] in
  Term.(const lsp_main $ log_file $ std $ vo_load_path $ ml_include_path),
  Term.info "coq-lsp" ~version:"0.01" ~doc ~man

let main () =
  match Term.eval lsp_cmd with
  | `Error _ -> exit 1
  | _        -> exit 0

let _ = main ()
