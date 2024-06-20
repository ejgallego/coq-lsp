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

type patvar = Pattern.patvar [@@deriving sexp,yojson,hash,compare]

type case_info_pattern = Pattern.case_info_pattern

val case_info_pattern_of_sexp : Sexp.t -> case_info_pattern
val sexp_of_case_info_pattern : case_info_pattern -> Sexp.t

type constr_pattern = Pattern.constr_pattern
  [@@deriving sexp,yojson,hash,compare]
