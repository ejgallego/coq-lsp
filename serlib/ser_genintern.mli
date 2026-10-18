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

module Store : SerType.SJHC with type t = Genintern.Store.t

type intern_variable_status = Genintern.intern_variable_status
  [@@deriving sexp, yojson, hash, compare]

type glob_sign = Genintern.glob_sign

val glob_sign_of_sexp : Sexp.t -> glob_sign
val sexp_of_glob_sign : glob_sign -> Sexp.t

type glob_constr_and_expr = Genintern.glob_constr_and_expr
  [@@deriving sexp, yojson, hash, compare]

type glob_constr_pattern_and_expr = Genintern.glob_constr_pattern_and_expr
  [@@deriving sexp, yojson, hash, compare]
