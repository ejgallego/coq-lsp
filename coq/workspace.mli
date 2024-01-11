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
(* Copyright 2019-2022 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Flags : sig
  type t = private
    { indices_matter : bool
    ; impredicative_set : bool
    }
end

module Warning : sig
  type t

  val make : string -> t

  (** Adds new warnings to the list of current warnings, the Coq API here is a
      bit tricky... *)
  val apply : t list -> unit
end

module Module : sig
  type t
end

type t = private
  { coqlib : string
  ; coqcorelib : string
  ; ocamlpath : string option
  ; vo_load_path : Loadpath.vo_path list
  ; ml_include_path : string list
  ; require_libs :
      (string * string option * Vernacexpr.export_with_cats option) list
  ; flags : Flags.t
  ; warnings : Warning.t list
  ; modules : Module.t list
  ; kind : string  (** How the workspace was built *)
  ; debug : bool  (** Enable backtraces *)
  }

(** compare *)
val compare : t -> t -> int

(** hash *)
val hash : t -> int

(** user message, debug extra data *)
val describe : t -> string * string

module CmdLine : sig
  type t =
    { coqlib : string
    ; coqcorelib : string
    ; ocamlpath : string option
    ; vo_load_path : Loadpath.vo_path list
    ; ml_include_path : string list
    ; args : string list
    ; require_libraries : (string option * string) list  (** Library, From *)
    }
end

val guess : debug:bool -> cmdline:CmdLine.t -> dir:string -> t

(** [apply libname w] will prepare Coq for a new file [libname] on workspace [w] *)
val apply : uri:Lang.LUri.File.t -> t -> unit

(** *)
val dirpath_of_uri : uri:Lang.LUri.File.t -> Names.DirPath.t
