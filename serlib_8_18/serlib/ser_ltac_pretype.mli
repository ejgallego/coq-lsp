(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type closure = Ltac_pretype.closure

val closure_of_sexp : Sexp.t -> closure
val sexp_of_closure : closure -> Sexp.t

type closed_glob_constr = Ltac_pretype.closed_glob_constr
  [@@deriving sexp,hash,compare]

type constr_under_binders = Ltac_pretype.constr_under_binders

val constr_under_binders_of_sexp : Sexp.t -> constr_under_binders
val sexp_of_constr_under_binders : constr_under_binders -> Sexp.t
