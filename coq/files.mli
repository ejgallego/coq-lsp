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
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias & Bhakti Shah                    *)
(************************************************************************)

type t [@@deriving hash, compare]

val make : unit -> t

(** [bump ()] Signal the files have changed *)
val bump : t -> t

(** Check if a file is ready *)
module Require_result : sig
  type t =
    | Ready of
        (Names.DirPath.t * CUnix.physical_path, Loadpath.Error.t) Result.t list
    | Wait of CUnix.physical_path list
end

val requires_are_ready : files:t -> Ast.Require.t -> Require_result.t
