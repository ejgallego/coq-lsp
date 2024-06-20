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

open Sexplib

type t = EConstr.t
  [@@deriving sexp,yojson,hash,compare]

type existential = EConstr.existential

val existential_of_sexp : Sexp.t -> existential
val sexp_of_existential : existential -> Sexp.t

type constr = t
  [@@deriving sexp,yojson,hash,compare]

type types = t

val sexp_of_types : types -> Sexp.t
val types_of_sexp : Sexp.t -> types

type unsafe_judgment = EConstr.unsafe_judgment

val sexp_of_unsafe_judgment : unsafe_judgment -> Sexp.t
val unsafe_judgment_of_sexp : Sexp.t -> unsafe_judgment
