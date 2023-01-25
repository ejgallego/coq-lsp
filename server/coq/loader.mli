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

(** [plugin_handler user_loader] Plugin loader that will also load the
    instrumentation plugins for serlib if those available. [user_loader] can be
    used to override the default of [Fl_dynload.load_packages] as loader. *)
val plugin_handler : (string list -> unit) option -> Mltop.PluginSpec.t -> unit
