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

  let pp fmt { line; character; offset } =
    Format.fprintf fmt "{ l: %d, c: %d | o: %d }" line character offset
end

module Range = struct
  type t =
    { start : Point.t
    ; end_ : Point.t
    }

  let pp fmt { start; end_ } =
    Format.fprintf fmt "(@[%a@]--@[%a@])" Point.pp start Point.pp end_

  let to_string r = Format.asprintf "%a" pp r
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
    ; message : Pp.t
    ; extra : Extra.t list option
    }
end
