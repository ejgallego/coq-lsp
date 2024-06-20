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

type 'a or_var = 'a Locus.or_var
  [@@deriving sexp,yojson,hash,compare]

type 'a occurrences_gen = 'a Locus.occurrences_gen
[@@deriving sexp, yojson, hash,compare]

type occurrences_expr = Locus.occurrences_expr

val occurrences_expr_of_sexp : Sexp.t -> occurrences_expr
val sexp_of_occurrences_expr : occurrences_expr -> Sexp.t

type 'a with_occurrences_expr = 'a Locus.with_occurrences_expr [@@deriving sexp, yojson, hash,compare]
type 'a with_occurrences = 'a Locus.with_occurrences [@@deriving sexp, yojson, hash,compare]

type occurrences = Locus.occurrences
[@@deriving sexp, yojson, hash,compare]

type hyp_location_flag = Locus.hyp_location_flag
  [@@deriving sexp,hash,compare]

type 'a hyp_location_expr = 'a Locus.hyp_location_expr
val hyp_location_expr_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a hyp_location_expr
val sexp_of_hyp_location_expr : ('a -> Sexp.t) -> 'a hyp_location_expr -> Sexp.t

type 'id clause_expr = 'id Locus.clause_expr
  [@@deriving sexp,yojson,hash,compare]

type clause = Locus.clause

val clause_of_sexp : Sexp.t -> clause
val sexp_of_clause : clause -> Sexp.t

type clause_atom = Locus.clause_atom

val clause_atom_of_sexp : Sexp.t -> clause_atom
val sexp_of_clause_atom : clause_atom -> Sexp.t

type concrete_clause = Locus.concrete_clause

val concrete_clause_of_sexp : Sexp.t -> concrete_clause
val sexp_of_concrete_clause : concrete_clause -> Sexp.t

type hyp_location = Locus.hyp_location
  [@@deriving sexp,yojson,hash,compare]

type goal_location = Locus.goal_location

val goal_location_of_sexp : Sexp.t -> goal_location
val sexp_of_goal_location : goal_location -> Sexp.t

type simple_clause = Locus.simple_clause
val simple_clause_of_sexp : Sexp.t -> simple_clause
val sexp_of_simple_clause : simple_clause -> Sexp.t

type 'id or_like_first = 'id Locus.or_like_first

val or_like_first_of_sexp : (Sexp.t -> 'id) -> Sexp.t -> 'id or_like_first
val sexp_of_or_like_first : ('id -> Sexp.t) -> 'id or_like_first -> Sexp.t
