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

type binding_kind = Glob_term.binding_kind [@@deriving sexp,yojson,hash,compare]
type 'a glob_sort_gen = 'a Glob_term.glob_sort_gen [@@deriving sexp,yojson,hash,compare]

type glob_level = Glob_term.glob_level
 [@@deriving sexp,yojson,hash,compare]

type glob_sort = Glob_term.glob_sort
 [@@deriving sexp,yojson,hash,compare]

(* type 'a cast_type = 'a Glob_term.cast_type
 * val cast_type_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a Glob_term.cast_type
 * val sexp_of_cast_type : ('a -> Sexp.t) -> 'a Glob_term.cast_type -> Sexp.t
 * val cast_type_of_yojson : (Yojson.Safe.t -> ('a,string) result ) -> Yojson.Safe.t -> ('a cast_type, string) Result.t
 * val cast_type_to_yojson : ('a -> Yojson.Safe.t) -> 'a cast_type -> Yojson.Safe.t *)

type glob_constraint = Glob_term.glob_constraint
 [@@deriving sexp,yojson,hash,compare]

type existential_name = Glob_term.existential_name [@@deriving sexp,yojson,hash,compare]
type cases_pattern    = Glob_term.cases_pattern

type glob_constr        = Glob_term.glob_constr
and glob_decl           = Glob_term.glob_decl
and predicate_pattern   = Glob_term.predicate_pattern
and tomatch_tuple       = Glob_term.tomatch_tuple
and tomatch_tuples      = Glob_term.tomatch_tuples
and cases_clause        = Glob_term.cases_clause
and cases_clauses       = Glob_term.cases_clauses
  [@@deriving sexp,yojson,hash,compare]
