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
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

let request ~token:_ ~doc ~point =
  let approx = Fleche.Info.Exact in
  match Fleche.Info.LC.node ~doc ~point approx with
  | None -> Ok `Null
  | Some node ->
    let range = Fleche.Doc.Node.range node in
    let parent = None in
    let answer = Lsp.Core.SelectionRange.({ range; parent } |> to_yojson) in
    Ok (`List [ answer ])
