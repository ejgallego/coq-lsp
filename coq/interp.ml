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
(* Copyright 2019-2022 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Info = struct
  type 'a t =
    { res : 'a
    ; goal : Goals.reified_pp option
    ; feedback : Pp.t Loc.located list
    }
end

let get_feedback fb_queue =
  let res = !fb_queue in
  fb_queue := [];
  res

(* let pr_goal (st : Coq_state.t) : Pp.t option =
 *   let st = Coq_state.to_coq st in
 *   Option.map
 *     (Vernacstate.LemmaStack.with_top ~f:(fun pstate ->
 *          let proof = Declare.Proof.get pstate in
 *          Printer.pr_open_subgoals ~quiet:false ~diffs:None proof))
 *     st.Vernacstate.lemmas *)

(* Move to utility functions indepedent of Stm *)
let if_not_empty (pp : Pp.t) =
  if Pp.(repr pp = Ppcmd_empty) then None else Some pp

let reify_goals ppx lemmas =
  let open Goals in
  let proof =
    Vernacstate.LemmaStack.with_top lemmas ~f:(fun pstate ->
        Declare.Proof.get pstate)
  in
  let { Proof.goals; stack; sigma; _ } = Proof.data proof in
  let ppx = List.map (Goals.process_goal_gen ppx sigma) in
  Some
    { goals = ppx goals
    ; stack = List.map (fun (g1, g2) -> (ppx g1, ppx g2)) stack
    ; bullet = if_not_empty @@ Proof_bullet.suggest proof
    ; shelf = Evd.shelf sigma |> ppx
    ; given_up = Evd.given_up sigma |> Evar.Set.elements |> ppx
    }

let pr_goal st =
  let ppx env sigma x =
    (* Jscoq_util.pp_opt *) Printer.pr_ltype_env env sigma x
  in
  let lemmas = State.lemmas ~st in
  Option.cata (reify_goals ppx) None lemmas

type 'a interp_result = 'a Info.t Protect.R.t

let coq_interp ~st cmd =
  let st = State.to_coq st in
  let cmd = Ast.to_coq cmd in
  Vernacinterp.interp ~st cmd |> State.of_coq

let interp ~st ~fb_queue cmd =
  Protect.eval cmd ~f:(fun cmd ->
      let res = coq_interp ~st cmd in
      (* It is safe to call the printer here as the state is guaranteed to be
         the right one after `coq_interp`, but beware! *)
      let goal = pr_goal res in
      let feedback = List.rev @@ get_feedback fb_queue in
      { Info.res; goal; feedback })

let marshal_out f oc res =
  match res with
  | Protect.R.Interrupted -> ()
  | Protect.R.Completed res -> (
    match res with
    | Ok res ->
      Marshal.to_channel oc 0 [];
      f oc res.Info.res
    | Error (loc, msg) ->
      Marshal.to_channel oc 1 [];
      Marshal.to_channel oc loc [];
      Marshal.to_channel oc msg [];
      ())

let marshal_in f ic =
  let tag : int = Marshal.from_channel ic in
  if tag = 0 then
    let res = f ic in
    Protect.R.Completed (Ok { Info.res; goal = None; feedback = [] })
  else
    let loc : Loc.t option = Marshal.from_channel ic in
    let msg : Pp.t = Marshal.from_channel ic in
    Protect.R.Completed (Error (loc, msg))
