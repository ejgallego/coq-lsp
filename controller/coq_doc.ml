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

module LSP = Lsp_base

type ast = Vernacexpr.vernac_control CAst.t

type node =
  { ast  : ast
  ; exec : bool
  ; goal : Pp.t option
  }

(* Private. A doc is a list of nodes for now. The first element in
   the list is assumed to be the tip of the document. The initial
   document is the empty list.
*)
type t =
  { uri : string
  ; version: int
  ; contents : string
  ; root : Vernacstate.t
  ; nodes : node list
  }

(* let mk_error ~doc pos msg =
 *   LSP.mk_diagnostics ~uri:doc.uri ~version:doc.version [pos, 1, msg, None] *)

type 'a result = Ok of 'a | Error of Loc.t option * Pp.t

let create ~uri ~version ~contents =
  { uri
  ; contents
  ; version
  ; root = begin
      let root_state = Option.(get !Coq_init.root_state) in
      Vernacstate.unfreeze_interp_state root_state;
      let dp = Names.(DirPath.make [Id.of_string "foo"]) in
      Declaremods.start_library dp;
      Vernacstate.freeze_interp_state ~marshallable:false
    end
  ; nodes = []
  }

(* XXX: Save on close? *)
(* let close_doc _modname = () *)

let coq_protect f x =
  try let res = f x in Ok res
  with exn ->
  let (e, info) = CErrors.push exn in
  (* XXX: This is madness in Coq upstream, we should fix it *)
  let (e, info) = ExplainErr.process_vernac_interp_error (e, info) in
  let loc = Loc.(get_loc info) in
  let msg = CErrors.iprint (e, info) in
  Error (loc, msg)

let parse_stm ~st ps =
  let mode = Option.map Vernacentries.(fun _ -> get_default_proof_mode ()) st.Vernacstate.proof in
  coq_protect Vernacstate.(Parser.parse st.parsing Pvernac.(main_entry mode)) ps

let interp_command ~st stm =
  coq_protect (Vernacentries.interp ~st) stm

(* Read the input stream until a dot is encountered *)
let parse_to_dot =
  let rec dot st = match Stream.next st with
    | Tok.KEYWORD ("."|"...") -> ()
    | Tok.EOI -> ()
    | _ -> dot st
  in
  Pcoq.Entry.of_parser "Coqtoplevel.dot" dot

(* If an error occurred while parsing, we try to read the input until a dot
   token is encountered.
   We assume that when a lexer error occurs, at least one char was eaten *)

let rec discard_to_dot ps =
  try
    Pcoq.Entry.parse parse_to_dot ps
  with
    | CLexer.Error.E _ -> discard_to_dot ps
    | e when CErrors.noncritical e -> ()

let pr_goal (st : Vernacstate.t) : Pp.t option =
  Option.map (fun pstate ->
      let proof = Lemmas.(pf_fold Proof_global.give_me_the_proof) pstate in
      Printer.pr_open_subgoals ~proof) st.Vernacstate.proof

type process_action = | EOF | Skip | Process of Vernacexpr.vernac_control CAst.t

(* XXX: Imperative problem *)
let process_and_parse doc =
  let doc_handle = Pcoq.Parsable.make Stream.(of_string doc.contents) in
  let rec stm doc st diags =
    Lsp_io.log_error "coq" "parsing sentence";
    (* Parsing *)
    let action, diags =
      match parse_stm ~st doc_handle with
      | Ok None ->
        EOF, diags
      | Ok (Some ast) ->
        Process ast, diags
      | Error(loc, msg) ->
        let diags = (loc, 1, msg, None) :: diags in
        discard_to_dot doc_handle;
        Skip, diags
    in
    (* Execution *)
    match action with
    (* End of file *)
    | EOF ->
      doc, st, diags
    | Skip ->
      stm doc st diags
    (* We interpret the command now *)
    | Process ast ->
      match interp_command ~st ast with
      | Ok st ->
        (* let ok_diag = node.pos, 4, "OK", !Proofs.theorem in *)
        let ok_diag = ast.CAst.loc, 4, Pp.(str "OK"), None in
        let diags = ok_diag :: diags in
        let node = { ast; exec = true; goal = pr_goal st } in
        let doc = { doc with nodes = node :: doc.nodes } in
        stm doc st diags
      | Error (loc, msg) ->
        let loc = Option.append loc ast.CAst.loc in
        let diags = (loc, 1, msg, None) :: diags in
        let node = { ast; exec = false; goal = None } in
        let doc = { doc with nodes = node :: doc.nodes } in
        stm doc st diags
  in
  stm doc doc.root []

let check ~doc =
  let uri, version = doc.uri, doc.version in

  (* Start library *)
  let doc, st, diags = process_and_parse doc in
  doc, st, LSP.mk_diagnostics ~uri ~version @@ List.fold_left (fun acc (pos,lvl,msg,goal) ->
      match pos with
      | None     -> acc
      | Some pos -> (pos,lvl,msg,goal) :: acc
    ) [] diags
