(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2020 MINES ParisTech / INRIA                          *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

open Sexplib.Std

module Names  = Ser_names
module Evar   = Ser_evar
module Sorts  = Ser_sorts
module Constr = Ser_constr
module Univ   = Ser_univ

module NVI = struct
  type t = Nativevalues.t
  let name = "Nativevalues.t"
end

include SerType.Opaque(NVI)

type tag =
  [%import: Nativevalues.tag]
  [@@deriving sexp]

type arity =
  [%import: Nativevalues.arity]
  [@@deriving sexp]

type reloc_table =
  [%import: Nativevalues.reloc_table]
  [@@deriving sexp]

type annot_sw =
  [%import: Nativevalues.annot_sw]
  [@@deriving sexp]

type symbol =
  [%import: Nativevalues.symbol]
  [@@deriving sexp]

type symbols =
  [%import: Nativevalues.symbols]
  [@@deriving sexp]
