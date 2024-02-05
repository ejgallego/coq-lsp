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

let char_of_index ~lines ~line ~byte =
  if line < Array.length lines then
    let line = Array.get lines line in
    match Utf8.char_of_index ~line ~byte with
    | Some char -> char
    | None -> Utf8.length line
  else 0

let to_range ~lines (p : Loc.t) : Lang.Range.t =
  let Loc.{ line_nb; line_nb_last; bol_pos; bol_pos_last; bp; ep; _ } = p in

  let start_line = line_nb - 1 in
  let end_line = line_nb_last - 1 in

  (* cols *)
  let start_col = bp - bol_pos in
  let end_col = ep - bol_pos_last in

  let start_col = char_of_index ~lines ~line:start_line ~byte:start_col in
  let end_col = char_of_index ~lines ~line:end_line ~byte:end_col in
  Lang.Range.
    { start = { line = start_line; character = start_col; offset = bp }
    ; end_ = { line = end_line; character = end_col; offset = ep }
    }

let to_orange ~lines = Option.map (to_range ~lines)

(* Separation of parsing and execution made upstream API hard to use for us
   :/ *)
let pmeasure (measure, print) fn =
  match measure fn () with
  | Ok _ as r -> Feedback.msg_notice @@ print r
  | Error (exn, _) as r ->
    Feedback.msg_notice @@ print r;
    Exninfo.iraise exn

let with_fail fn =
  try
    fn ();
    CErrors.user_err (Pp.str "The command has not failed!")
  with exn when CErrors.noncritical exn ->
    let exn = Exninfo.capture exn in
    let msg = CErrors.iprint exn in
    Feedback.msg_notice ?loc:None
      Pp.(str "The command has indeed failed with message:" ++ fnl () ++ msg)

let with_ctrl ctrl ~st ~fn =
  let st = State.to_coq st in
  match ctrl with
  | Vernacexpr.ControlTime ->
    pmeasure System.(measure_duration, fmt_transaction_result) fn
  | Vernacexpr.ControlTimeout n -> (
    match Control.timeout (float_of_int n) fn () with
    | None -> Exninfo.iraise (Exninfo.capture CErrors.Timeout)
    | Some x -> x)
  (* fail and succeed *)
  | Vernacexpr.ControlFail ->
    with_fail fn;
    Vernacstate.Interp.invalidate_cache ();
    Vernacstate.unfreeze_full_state st
  | Vernacexpr.ControlSucceed ->
    fn ();
    Vernacstate.Interp.invalidate_cache ();
    Vernacstate.unfreeze_full_state st
  (* Unsupported by coq-lsp, maybe deprecate upstream *)
  | Vernacexpr.ControlRedirect _ -> fn ()

let with_control ~fn ~control ~st =
  List.fold_right (fun ctrl fn () -> with_ctrl ctrl ~st ~fn) control fn ()
