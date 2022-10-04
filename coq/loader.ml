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

(* Should improve *)
let map_serlib fl_pkg =
  let supported = match fl_pkg with
    (* Supported by serlib *)             (* directory   *)
    | "coq-core.plugins.ltac"             (* ltac        *)
    | "coq-core.plugins.firstorder"       (* firstorder  *)
    | "coq-core.plugins.funind"           (* funind      *)
    | "coq-core.plugins.ring"             (* ring        *)
    | "coq-core.plugins.extraction"       (* extraction  *)
    | "coq-core.plugins.ssrmatching"      (* ssrmatching *)
    | "coq-core.plugins.ssreflect"        (* ssr *)
      -> true
    | _ ->
      Feedback.msg_warning Pp.(str "Missing serlib plugin: " ++ str fl_pkg);
      false
  in
  if supported
  then
    let plugin_name = String.split_on_char '.' fl_pkg |> list_last in
    Some ("coq-serapi.serlib." ^ plugin_name)
  else None

let plugin_handler user_handler =
  let loader = Option.default (Fl_dynload.load_packages ~debug:false) user_handler in
  fun fl_pkg ->
    let _, fl_pkg = Mltop.PluginSpec.repr fl_pkg in
    match map_serlib fl_pkg with
    | Some serlib_pkg ->
      loader [serlib_pkg]
    | None ->
      loader [fl_pkg]
