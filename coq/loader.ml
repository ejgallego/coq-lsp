(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* coq-lsp / SerAPI                                                     *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2024 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

[@@@ocamlformat "disable"]

let list_last l = List.(nth l (length l - 1))

let not_available_warn fl_pkg info =
    Feedback.msg_warning
      Pp.(str "Serlib plugin: " ++ str fl_pkg
          ++ str " is not available" ++ str info ++ str "." ++ fnl ()
          ++ str "Incremental checking for commands in this plugin will be impacted.")

let check_package_exists fl_pkg =
  try
    let _ = Findlib.package_directory fl_pkg in
    Some fl_pkg
  with
  | Findlib.No_such_package (_, info) ->
    not_available_warn fl_pkg info;
    None

(* Should improve *)
let map_serlib fl_pkg =
  let supported = match fl_pkg with
    (* Supported by serlib *)             (* directory   *)
    | "rocq-runtime.plugins.btauto"           (* btauto *)
    | "rocq-runtime.plugins.cc_core"          (* cc_core  *)
    | "rocq-runtime.plugins.cc"               (* cc  *)
    | "rocq-runtime.plugins.extraction"       (* extraction  *)
    | "rocq-runtime.plugins.firstorder_core"  (* firstorder_core  *)
    | "rocq-runtime.plugins.firstorder"       (* firstorder  *)
    | "rocq-runtime.plugins.funind"           (* funind      *)
    | "rocq-runtime.plugins.ltac"             (* ltac        *)
    | "rocq-runtime.plugins.ltac2"            (* ltac2       *)
    | "rocq-runtime.plugins.ltac2_ltac1"      (* ltac2_ltac1 *)
    | "rocq-runtime.plugins.micromega"        (* micromega   *)
    | "rocq-runtime.plugins.micromega_core"   (* micromega_core *)
    | "rocq-runtime.plugins.ring"             (* ring        *)
    | "rocq-runtime.plugins.ssreflect"        (* ssreflect   *)
    | "rocq-runtime.plugins.ssrmatching"      (* ssrmatching *)
    | "rocq-runtime.plugins.number_string_notation" (* syntax *)
    | "rocq-runtime.plugins.tauto"            (* tauto *)
    | "rocq-runtime.plugins.zify"             (* zify *)
      -> true
    | _ ->
      not_available_warn fl_pkg ": serlib support is missing";
      false
  in
  if supported
  then
    let plugin_name = String.split_on_char '.' fl_pkg |> list_last in
    let serlib_name = "coq-lsp.serlib." ^ plugin_name in
    check_package_exists serlib_name
  else None

(* We used to be liberal here in the case a SerAPI plugin was not available.
   This proved to be a bad choice as Coq got confused when plugin loading
   failed. Par-contre, we now need to make the list in `map_serlib` open, so
   plugins can register whether they support serialization. I'm afraid that'll
   have to happen via the finlib database as we cannot load anticipatedly a
   plugin that may not exist. *)
let safe_loader loader fl_pkg =
  try loader [fl_pkg]
  with
    exn ->
    let iexn = Exninfo.capture exn in
    let exn_msg = CErrors.iprint iexn in
     Feedback.msg_warning
      Pp.(str "Loading findlib plugin: " ++ str fl_pkg
          ++ str "failed" ++ fnl () ++ exn_msg);
    Exninfo.iraise iexn

let default_loader pkgs : unit =
  Fl_dynload.load_packages ~debug:false pkgs

let plugin_handler user_loader =
  let loader = Option.default default_loader user_loader in
  let safe_loader = safe_loader loader in
  fun fl_pkg ->
    let fl_pkg = Mltop.PluginSpec.to_package fl_pkg in
    match map_serlib fl_pkg with
    | Some serlib_pkg ->
      safe_loader serlib_pkg
    | None ->
      safe_loader fl_pkg
