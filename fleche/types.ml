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

(* XXX: ejgallego, do we start lines at 0? *)
module Point = struct
  type t =
    { line : int
    ; character : int
    ; offset : int
    }
end

module Range = struct
  type t =
    { start : Point.t
    ; end_ : Point.t
    }
end

module Diagnostic = struct
  module Extra = struct
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

let to_range (p : Loc.t) : Range.t =
  let Loc.{ line_nb; line_nb_last; bol_pos; bol_pos_last; bp; ep; _ } = p in
  let start_line = line_nb - 1 in
  let start_col = bp - bol_pos in
  let end_line = line_nb_last - 1 in
  let end_col = ep - bol_pos_last in
  Range.
    { start = { line = start_line; character = start_col; offset = bp }
    ; end_ = { line = end_line; character = end_col; offset = ep }
    }

let to_orange = Option.map to_range
