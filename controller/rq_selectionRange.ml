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

let point_to_result ~doc ((line, character) as point) =
  let approx = Fleche.Info.Exact in
  let range =
    match Fleche.Info.LC.node ~doc ~point approx with
    | None ->
      let point = { Lang.Point.line; character; offset = -1 } in
      { Lang.Range.start = point; end_ = point }
    | Some node -> Fleche.Doc.Node.range node
  in
  let parent = None in
  Lsp.Core.SelectionRange.{ range; parent }

let request ~points ~token:_ ~doc ~point:_ =
  let results = List.map (point_to_result ~doc) points in
  let answers = List.map Lsp.Core.SelectionRange.to_yojson results in
  Ok (`List answers)
