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
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(************************************************************************)
(* Status: Very Experimental                                            *)
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
