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

open Sexplib.Std

module Names  = Ser_names
module Evar   = Ser_evar
module Sorts  = Ser_sorts
module Constr = Ser_constr
module Univ   = Ser_univ
module UVars  = Ser_uvars

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
