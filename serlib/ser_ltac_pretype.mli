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

type closure = Ltac_pretype.closure

val closure_of_sexp : Sexp.t -> closure
val sexp_of_closure : closure -> Sexp.t

type closed_glob_constr = Ltac_pretype.closed_glob_constr
  [@@deriving sexp,hash,compare]

type constr_under_binders = Ltac_pretype.constr_under_binders

val constr_under_binders_of_sexp : Sexp.t -> constr_under_binders
val sexp_of_constr_under_binders : constr_under_binders -> Sexp.t
