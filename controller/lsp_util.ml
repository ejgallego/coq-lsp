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

module LSP = Lsp.Base

let lsp_of_diags ~uri ~version diags =
  List.map
    (fun { Fleche.Types.Diagnostic.range; severity; message; extra = _ } ->
      (range, severity, message, None))
    diags
  |> Lsp.Base.mk_diagnostics ~uri ~version

let lsp_of_progress ~uri ~version progress =
  let progress =
    List.map
      (fun (range, kind) ->
        `Assoc [ ("range", LSP.mk_range range); ("kind", `Int kind) ])
      progress
  in
  let params =
    [ ( "textDocument"
      , `Assoc [ ("uri", `String uri); ("version", `Int version) ] )
    ; ("processing", `List progress)
    ]
  in
  LSP.mk_notification ~method_:"$/coq/fileProgress" ~params
