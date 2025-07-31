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

module Environ   = Ser_environ
module Reduction = Ser_reduction
module Constr    = Ser_constr

type econstr =
  [%import: Evd.econstr]

(* ahhh *)
let econstr_of_sexp s = Evd.MiniEConstr.of_constr (Constr.t_of_sexp s)
let sexp_of_econstr c = Constr.sexp_of_t (Evd.MiniEConstr.unsafe_to_constr c)

type conv_pb = Reduction.conv_pb
  [@@deriving sexp]

type evar_constraint =
  [%import: Evd.evar_constraint]
  [@@deriving sexp]

type unsolvability_explanation =
  [%import: Evd.unsolvability_explanation]
  [@@deriving sexp]
