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
(* Copyright 2022-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

let to_range ~lines (p : Loc.t) : Types.Range.t =
  let Loc.{ line_nb; line_nb_last; bol_pos; bol_pos_last; bp; ep; _ } = p in

  let start_line = line_nb - 1 in
  let end_line = line_nb_last - 1 in

  (* cols *)
  let start_col = bp - bol_pos in
  let end_col = ep - bol_pos_last in

  let start_col =
    Utf8.char_of_byte ~line:(Array.get lines start_line) ~byte:start_col
  in
  let end_col =
    Utf8.char_of_byte ~line:(Array.get lines end_line) ~byte:end_col
  in
  Types.Range.
    { start = { line = start_line; character = start_col; offset = bp }
    ; end_ = { line = end_line; character = end_col; offset = ep }
    }

let to_orange ~lines = Option.map (to_range ~lines)
