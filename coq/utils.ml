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

(* We convert in case of failure to some default values *)

let utf16_offset_of_utf8_offset ~lines ~line ~byte =
  if line < Array.length lines then
    let line = Array.get lines line in
    Lang.Utf.utf16_offset_of_utf8_offset ~line ~offset:byte
  else 0

let to_range ~lines (p : Loc.t) : Lang.Range.t =
  let Loc.{ line_nb; line_nb_last; bol_pos; bol_pos_last; bp; ep; _ } = p in

  let start_line = line_nb - 1 in
  let end_line = line_nb_last - 1 in

  (* cols *)
  let start_col = bp - bol_pos in
  let end_col = ep - bol_pos_last in

  let start_col =
    utf16_offset_of_utf8_offset ~lines ~line:start_line ~byte:start_col
  in
  let end_col =
    utf16_offset_of_utf8_offset ~lines ~line:end_line ~byte:end_col
  in
  Lang.Range.
    { start = { line = start_line; character = start_col; offset = bp }
    ; end_ = { line = end_line; character = end_col; offset = ep }
    }

let to_orange ~lines = Option.map (to_range ~lines)

let with_control ~fn ~control ~st =
  let open VernacControl in
  let control = from_syntax control in
  let control, () =
    under_control ~loc:None ~with_local_state:trivial_state control ~noop:() fn
  in
  let noop = after_last_phase ~loc:None control in
  let () =
    if noop then (
      Vernacstate.Interp.invalidate_cache ();
      Vernacstate.unfreeze_full_state (State.to_coq st))
  in
  ()
