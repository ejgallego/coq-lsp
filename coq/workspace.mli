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
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Flags : sig
  type t = private
    { impredicative_set : bool
    ; indices_matter : bool
    ; type_in_type : bool
    ; rewrite_rules : bool
    }
end

module Warning : sig
  type t

  val make : string -> t

  (** Adds new warnings to the list of current warnings, the Coq API here is a
      bit tricky... *)
  val apply : t list -> unit
end

module Require : sig
  type t =
    { library : string
    ; from : string option
    ; flags : Vernacexpr.export_with_cats option
    }
end

(* Generated from a _CoqProject, dune (in the future) or command line args *)
type t = private
  { coqlib : string  (** Path to coqlib *)
  ; findlib_config : string option
        (** Path to findlib config file, if [None], default *)
  ; ocamlpath : string list
        (** extra ocamlpath paths, for example for local plugins *)
  ; vo_load_path : Loadpath.vo_path list
        (** List of -R / -Q flags passed to Coq, usually theories we depend on *)
  ; require_libs : Require.t list
        (** Modules to preload, usually Coq.Init.Prelude *)
  ; flags : Flags.t  (** Coq-specific flags *)
  ; warnings : Warning.t list
  ; kind : string  (** How the workspace was built *)
  ; debug : bool  (** Enable backtraces *)
  }

(** Inject some requires *)
val inject_requires : extra_requires:Require.t list -> t -> t

(** compare *)
val compare : t -> t -> int

(** hash *)
val hash : t -> int

(** [describe w] return [user, extra], where [user] is the relevant user
    message, and [extra] contains lower-level debug data such as all findlib
    packages in scope, etc... data *)
val describe : t -> string * string

val describe_guess : (t, string) Result.t -> string * string

module CmdLine : sig
  type t =
    { coqlib : string
    ; findlib_config : string option
    ; ocamlpath : string list
    ; vo_load_path : Loadpath.vo_path list
    ; args : string list
    ; require_libraries : (string option * string) list  (** Library, From *)
    }
end

val guess :
     token:Limits.Token.t
  -> debug:bool
  -> cmdline:CmdLine.t
  -> dir:string
  -> (t, string) Result.t

(* Fallback workspace *)
val default : debug:bool -> cmdline:CmdLine.t -> t

(** [apply libname w] will prepare Coq for a new file [libname] on workspace [w] *)
val apply : intern:unit -> uri:Lang.LUri.File.t -> t -> unit

(** *)
val dirpath_of_uri : uri:Lang.LUri.File.t -> Names.DirPath.t
