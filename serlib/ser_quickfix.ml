(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

module Loc = Ser_loc
module Pp  = Ser_pp

module QFB = struct

  type t = Quickfix.t
  type _t = Loc.t * Pp.t
  [@@deriving sexp,yojson,hash,compare]

  let of_t qf = Quickfix.(loc qf, pp qf)
  let to_t (loc, pp) = Quickfix.make ~loc pp
end

include SerType.Biject(QFB)
