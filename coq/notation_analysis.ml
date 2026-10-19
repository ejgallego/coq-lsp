(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Concrete syntax of the mathematical vernacular MV V2.6 *)

open Vernacexpr
open Synterp
open Constrintern

let with_def_attributes ~atts f =
  let atts = Attributes.parse Vernacentries.DefAttributes.def_attributes atts in
  if atts.program then Declare.Obls.check_program_libraries ();
  f ~atts

open Constrexpr

let save_notation accu intenv loc ntn ntnargs =
  (* Adjust to parsing of { } *)
  let ntn, fullargs = Constrexpr_ops.contract_curly_brackets ntn ntnargs in
  (* Recover interpretation { } *)
  let _, df = Notation.interp_notation ?loc ntn (intern_subscopes intenv) in
  let posl = Constrexpr_ops.ntn_loc ?loc fullargs ntn in
  let ((path, secpath, _), _), sc = df in
  accu :=
    ((List.map Loc.make_loc posl)
    , (Names.DirPath.to_string path)
    , (Names.DirPath.to_string secpath)
    , ntn.ntn_key
    , sc)
    :: !accu

let list_notations_interner accu (base:Interner.t) : Interner.t =
  let notation self env intenv lvar ?loc ((_, ntn, ntnargs) as v) =
    save_notation accu intenv loc ntn ntnargs;
    base.notation self env intenv lvar ?loc v
  in
  (* NB: default interner doesn't use open recursion for a CNotation head of application *)
  let app self env intenv lvar ?loc ((hd, _) as v) =
    let () = match hd.CAst.v with
      | CNotation (_, ntn, ntnargs) -> save_notation accu intenv hd.loc ntn ntnargs
      | _ -> ()
    in
    base.app self env intenv lvar ?loc v
  in
  { base with
    Constrintern.Interner.notation;
    app
  }

let list_notations_in_statement_lemma ~program_mode env0 evd thm =
  let _, (bl, t) = thm in
  let evd, (impls, ((env, _), _, _)) =
    Constrintern.interp_context_evars ~program_mode env0 evd bl
  in
  let accu = ref [] in
  let self = list_notations_interner accu Constrintern.default in
  let _ : Glob_term.glob_constr = Constrintern.intern_gen ~self IsType env evd ~impls t in
  !accu

let list_notations_in_statement_lemma_com ~typing_flags ~program_mode thm =
  let env0 = Global.env () in
  let env0 = Environ.update_typing_flags ?typing_flags env0 in
  let udecls = List.map (fun ((_, univs), _) -> univs) [ thm ] in
  let evd, _ = Constrintern.interp_mutual_univ_decl_opt env0 udecls in
  list_notations_in_statement_lemma ~program_mode env0 evd thm

let list_notations_in_statement_vernac_start_proof ~atts l =
  let open Vernacentries.DefAttributes in
  if Dumpglob.dump () then
    List.iter (fun ((id, _), _) -> Dumpglob.dump_definition id false "prf") l;
  (* TODO : remove *)
  let program_mode, typing_flags = (atts.program, atts.typing_flags) in
  List.concat
  @@ List.map
       (list_notations_in_statement_lemma_com ~typing_flags ~program_mode)
       l

let list_notations_in_statement_vernac ~atts v =
  match v with
  | VernacStartTheoremProof (_, l) ->
    with_def_attributes ~atts list_notations_in_statement_vernac_start_proof l
  | _ -> CErrors.anomaly (Pp.str "Only works in statements.")

let list_notations_in_statement_expr ~atts c =
  match c with
  | VernacSynterp _ -> assert false
  | VernacSynPure x -> list_notations_in_statement_vernac ~atts x

let list_notations_in_statement_control { CAst.v = cmd; _ } =
  with_generic_atts ~check:false cmd.attrs (fun ~atts ->
      list_notations_in_statement_expr ~atts cmd.expr)

(* XXX review *)
let list_notations_in_statement ~intern cmd =
  match cmd.CAst.v.expr with
  | VernacSynterp _ -> CErrors.anomaly (Pp.str "Only works in statements.")
  | VernacSynPure _ ->
    let entry = Synterp.synterp_control ~intern cmd in
    list_notations_in_statement_control entry

module Info = struct
  type t =
    { locations : Loc.t list
    ; path : string
    ; secpath : string
    ; notation : string
    ; scope : string option
    }

  let make (locations, path, secpath, notation, scope) =
    { locations; path; secpath; notation; scope }
end

let notations_in_statement ~intern cmd =
  let cmd = Ast.to_coq cmd in
  let res = list_notations_in_statement ~intern cmd in
  List.map Info.make res

let notations_in_statement ~token ~intern ~st cmd =
  let f = notations_in_statement ~intern in
  State.in_state ~token ~st ~f cmd
