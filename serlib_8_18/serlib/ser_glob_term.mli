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

type binding_kind = Glob_term.binding_kind [@@deriving sexp,yojson,hash,compare]
type 'a glob_sort_gen = 'a Glob_term.glob_sort_gen [@@deriving sexp,yojson,hash,compare]

type glob_level = Glob_term.glob_level
val glob_level_of_sexp : Sexp.t -> Glob_term.glob_level
val sexp_of_glob_level : Glob_term.glob_level -> Sexp.t

val glob_level_of_yojson : Yojson.Safe.t -> (glob_level,string) result
val glob_level_to_yojson : Glob_term.glob_level -> Yojson.Safe.t

type glob_sort = Glob_term.glob_sort
val glob_sort_of_sexp : Sexp.t -> Glob_term.glob_sort
val sexp_of_glob_sort : Glob_term.glob_sort -> Sexp.t
val glob_sort_of_yojson : Yojson.Safe.t -> (glob_sort, string) Result.result
val glob_sort_to_yojson : glob_sort -> Yojson.Safe.t

(* type 'a cast_type = 'a Glob_term.cast_type
 * val cast_type_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a Glob_term.cast_type
 * val sexp_of_cast_type : ('a -> Sexp.t) -> 'a Glob_term.cast_type -> Sexp.t
 * val cast_type_of_yojson : (Yojson.Safe.t -> ('a,string) result ) -> Yojson.Safe.t -> ('a cast_type, string) Result.result
 * val cast_type_to_yojson : ('a -> Yojson.Safe.t) -> 'a cast_type -> Yojson.Safe.t *)

type glob_constraint = Glob_term.glob_constraint
val glob_constraint_of_sexp : Sexp.t -> Glob_term.glob_constraint
val sexp_of_glob_constraint : Glob_term.glob_constraint -> Sexp.t
val glob_constraint_of_yojson : Yojson.Safe.t -> (glob_constraint, string) Result.result
val glob_constraint_to_yojson : glob_constraint -> Yojson.Safe.t

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
