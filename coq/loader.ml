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
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(* Copyright 2019-2022 Inria                                            *)
(* Written by Emilio J. Gallego Arias                                   *)
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
    | "coq-core.plugins.cc"               (* cc  *)
    | "coq-core.plugins.extraction"       (* extraction  *)
    | "coq-core.plugins.firstorder"       (* firstorder  *)
    | "coq-core.plugins.funind"           (* funind      *)
    | "coq-core.plugins.ltac"             (* ltac        *)
    | "coq-core.plugins.ltac2"            (* ltac2       *)
    | "coq-core.plugins.micromega"        (* micromega   *)
    | "coq-core.plugins.ring"             (* ring        *)
    | "coq-core.plugins.ssreflect"        (* ssreflect   *)
    | "coq-core.plugins.ssrmatching"      (* ssrmatching *)
    | "coq-core.plugins.number_string_notation" (* syntax *)
    | "coq-core.plugins.tauto"            (* tauto *)
    | "coq-core.plugins.zify"             (* zify *)
      -> true
    | _ ->
      not_available_warn fl_pkg ": serlib support is missing";
      false
  in
  if supported
  then
    let plugin_name = String.split_on_char '.' fl_pkg |> list_last in
    let serlib_name = "coq-serapi.serlib." ^ plugin_name in
    check_package_exists serlib_name
  else None

(* We are more liberal in the case a SerAPI plugin is not availabe, as
   the fallbacks are "safe", tho will yield way worse incremental
   behavior for expressions defined by the plugin *)
let safe_loader loader fl_pkg =
  try loader [fl_pkg]
  with
    exn ->
    let iexn = Exninfo.capture exn in
    let exn_msg = CErrors.iprint iexn in
     Feedback.msg_warning
      Pp.(str "Loading findlib plugin: " ++ str fl_pkg
          ++ str "failed" ++ fnl () ++ exn_msg);
    ()

let plugin_handler user_loader =
  let loader = Option.default (Fl_dynload.load_packages ~debug:false) user_loader in
  let safe_loader = safe_loader loader in
  fun fl_pkg ->
    let _, fl_pkg = Mltop.PluginSpec.repr fl_pkg in
    match map_serlib fl_pkg with
    | Some serlib_pkg ->
      safe_loader serlib_pkg
    | None ->
      safe_loader fl_pkg
