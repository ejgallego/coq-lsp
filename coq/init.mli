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
(* Coq Language Server Protocol / SerAPI                                *)
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(**************************************************************************)
(* Low-level, internal Coq initialization                                 *)
(**************************************************************************)

type opts =
  { msg_handler : Message.t -> unit  (** callback to handle async feedback *)
  ; load_module : string -> unit  (** callback to load cma/cmo files *)
  ; load_plugin : Mltop.PluginSpec.t -> unit
        (** callback to load findlib packages *)
  ; debug : bool  (** Enable Coq Debug mode *)
  }

val init : opts -> State.t

module Doc : sig
  type require_decl =
    string * string option * Vernacexpr.export_with_cats option

  type env =
    { vo_load_path : Loadpath.vo_path list
    ; ml_load_path : string list
    ; requires : require_decl list
    }

  val make : root_state:State.t -> env:env -> name:Names.DirPath.t -> State.t
end
