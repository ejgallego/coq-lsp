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

type 'a red_atom = 'a Genredexpr.red_atom

val red_atom_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a red_atom
val sexp_of_red_atom : ('a -> Sexp.t) -> 'a red_atom -> Sexp.t

type 'a glob_red_flag =  'a Genredexpr.glob_red_flag

val glob_red_flag_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a glob_red_flag
val sexp_of_glob_red_flag : ('a -> Sexp.t) -> 'a glob_red_flag -> Sexp.t
val glob_red_flag_of_yojson : (Yojson.Safe.t -> ('a, string) Result.result) -> Yojson.Safe.t -> ('a glob_red_flag, string) Result.result
val glob_red_flag_to_yojson : ('a -> Yojson.Safe.t) -> 'a glob_red_flag -> Yojson.Safe.t

type ('a, 'b, 'c) red_expr_gen =  ('a, 'b, 'c) Genredexpr.red_expr_gen
  [@@deriving sexp,yojson,hash,compare]

type ('a, 'b, 'c) may_eval =  ('a, 'b, 'c) Genredexpr.may_eval
  [@@deriving sexp,yojson,hash,compare]

type raw_red_expr = Genredexpr.raw_red_expr [@@deriving sexp,yojson,hash,compare]

type r_cst = Genredexpr.r_cst
  [@@deriving sexp,yojson,hash,compare]

type r_trm = Genredexpr.r_trm
  [@@deriving sexp,yojson,hash,compare]

type r_pat = Genredexpr.r_pat
  [@@deriving sexp,yojson,hash,compare]

type 'a and_short_name = 'a Genredexpr.and_short_name
  [@@deriving sexp,yojson,hash,compare]
