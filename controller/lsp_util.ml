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

let to_range (p : Loc.t) : Lsp.Base.range =
  let Loc.{ line_nb; line_nb_last; bol_pos; bol_pos_last; bp; ep; _ } = p in
  let start_line = line_nb - 1 in
  let start_col = bp - bol_pos in
  let end_line = line_nb_last - 1 in
  let end_col = ep - bol_pos_last in
  Lsp.Base.
    { start = { line = start_line; character = start_col }
    ; _end = { line = end_line; character = end_col }
    }

let to_orange = Option.map to_range
let to_msg x = Pp.string_of_ppcmds x
