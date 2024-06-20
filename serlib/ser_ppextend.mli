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

type ppbox = Ppextend.ppbox

val ppbox_of_sexp : Sexp.t -> ppbox
val sexp_of_ppbox : ppbox -> Sexp.t

type ppcut = Ppextend.ppcut

val ppcut_of_sexp : Sexp.t -> ppcut
val sexp_of_ppcut : ppcut -> Sexp.t

(* type unparsing = Ppextend.unparsing
 * val unparsing_of_sexp : Sexp.t -> unparsing
 * val sexp_of_unparsing : unparsing -> Sexp.t *)

type unparsing_rule = Ppextend.unparsing_rule
val unparsing_rule_of_sexp : Sexp.t -> unparsing_rule
val sexp_of_unparsing_rule : unparsing_rule -> Sexp.t

type notation_printing_rules = Ppextend.notation_printing_rules
val notation_printing_rules_of_sexp : Sexp.t -> notation_printing_rules
val sexp_of_notation_printing_rules : notation_printing_rules -> Sexp.t
