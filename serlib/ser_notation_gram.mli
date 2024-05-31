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

(* type parenRelation = Notation_gram.parenRelation
 * 
 * val parenRelation_of_sexp : Sexp.t -> parenRelation
 * val sexp_of_parenRelation : parenRelation -> Sexp.t
 * 
 * type precedence = Notation_gram.precedence
 * 
 * val precedence_of_sexp : Sexp.t -> precedence
 * val sexp_of_precedence : precedence -> Sexp.t
 * 
 * type tolerability = Notation_gram.tolerability
 * 
 * val tolerability_of_sexp : Sexp.t -> tolerability
 * val sexp_of_tolerability : tolerability -> Sexp.t *)

type grammar_constr_prod_item = Notation_gram.grammar_constr_prod_item
val grammar_constr_prod_item_of_sexp : Sexp.t -> grammar_constr_prod_item
val sexp_of_grammar_constr_prod_item : grammar_constr_prod_item -> Sexp.t

type notation_grammar = Notation_gram.notation_grammar
val notation_grammar_of_sexp : Sexp.t -> notation_grammar
val sexp_of_notation_grammar : notation_grammar -> Sexp.t

