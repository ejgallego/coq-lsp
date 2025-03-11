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

module Genarg = Ser_genarg

module RawTac = struct
  type t = Gentactic.raw_generic_tactic

  type _t = Genarg.raw_generic_argument
  [@@deriving sexp,hash,compare,yojson]

  let to_t = Gentactic.of_raw_genarg
  let of_t = Gentactic.to_raw_genarg
end

module BijectRawtac = SerType.Biject(RawTac)

type raw_generic_tactic = BijectRawtac.t
[@@deriving sexp,hash,compare,yojson]
