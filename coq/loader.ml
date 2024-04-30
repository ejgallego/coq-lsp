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

let ml_path = ref []

let add_ml_path path =
  ml_path := path :: !ml_path

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
    | "cc_plugin"               (* cc  *)
    | "extraction_plugin"       (* extraction  *)
    | "firstorder_plugin"       (* firstorder  *)
    | "funind_plugin"           (* funind      *)
    | "ltac_plugin"             (* ltac        *)
    | "ltac2_plugin"            (* ltac2       *)
    | "micromega_plugin"        (* micromega   *)
    | "ring_plugin"             (* ring        *)
    | "ssreflect_plugin"        (* ssreflect   *)
    | "ssrmatching_plugin"      (* ssrmatching *)
    | "number_plugin_string_notation" (* syntax *)
    | "tauto_plugin"            (* tauto *)
    | "zify_plugin"             (* zify *)
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
    let iexn = CErrors.push exn in
    let exn_msg = CErrors.iprint iexn in
     Feedback.msg_warning
      Pp.(str "Loading findlib plugin: " ++ str fl_pkg
          ++ str "failed" ++ fnl () ++ exn_msg);
    Exninfo.iraise iexn

let plugin_handler user_loader =
  let fl_loader = Option.default (Fl_dynload.load_packages ~debug:false) user_loader in
  let dl_loader = (List.iter Dynlink.loadfile) in
  let fl_safe_loader = safe_loader fl_loader in
  let dl_safe_loader = safe_loader dl_loader in
  fun ml_mod ->
    match map_serlib ml_mod with
    | Some serlib_pkg ->
      fl_safe_loader serlib_pkg
    | None ->
      let _, ml_file = System.find_file_in_path ~warn:true !ml_path ml_mod in
      (* Format.eprintf "Loading raw module: %s" ml_file; *)
      dl_safe_loader ml_file

