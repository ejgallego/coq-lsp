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

module Point : sig
  type t =
    { line : int
    ; character : int
    ; offset : int
    }
end

module Range : sig
  type t =
    { start : Point.t
    ; _end : Point.t
    }
end

module Diagnostic : sig
  type t =
    { range : Range.t
    ; severity : int
    ; message : string
    }
end

(** XXX specific to Coq *)
val to_range : Loc.t -> Range.t

val to_orange : Loc.t option -> Range.t option
