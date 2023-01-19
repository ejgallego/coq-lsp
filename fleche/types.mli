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

(** ATTENTION: [character] is a Unicode caracter position, thus from Coq that
    usually requires conversion, as it will report the column offset in bytes.
    But [offset] is in bytes for now, as our downstream clients prefer this
    format. *)
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
    ; end_ : Point.t
    }
end

module Diagnostic : sig
  module Extra : sig
    type t =
      | FailedRequire of
          { prefix : Libnames.qualid option
          ; refs : Libnames.qualid list
          }
  end

  type t =
    { range : Range.t
    ; severity : int
    ; message : string
    ; extra : Extra.t list
    }
end

(** XXX specific to Coq *)
val to_range : Loc.t -> Range.t

val to_orange : Loc.t option -> Range.t option
