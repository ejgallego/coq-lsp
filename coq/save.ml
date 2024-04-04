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
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(* Taken from sertop / Coq *)
let ensure_no_pending_proofs ~in_file ~st =
  match st.Vernacstate.interp.lemmas with
  | Some lemmas ->
    let pfs = Vernacstate.LemmaStack.get_all_proof_names lemmas in
    CErrors.user_err
      Pp.(
        str "There are pending proofs in file "
        ++ str in_file ++ str ": "
        ++ (pfs |> List.rev |> prlist_with_sep pr_comma Names.Id.print)
        ++ str ".")
  | None ->
    let pm = st.Vernacstate.interp.program in
    let what_for = Pp.str ("file " ^ in_file) in
    NeList.iter
      (fun pm -> Declare.Obls.check_solved_obligations ~what_for ~pm)
      pm

let save_vo ~st ~ldir in_file =
  let st = State.to_coq st in
  let () = ensure_no_pending_proofs ~in_file ~st in
  let out_vo = Filename.(remove_extension in_file) ^ ".vo" in
  let output_native_objects = false in
  let todo_proofs = Library.ProofsTodoNone in
  let () =
    Library.save_library_to todo_proofs ~output_native_objects ldir out_vo
  in
  ()

let save_vo ~token ~st ~ldir ~in_file =
  Protect.eval ~token ~f:(save_vo ~st ~ldir) in_file
