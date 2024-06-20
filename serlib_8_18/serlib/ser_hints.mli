(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

type hint_db_name = Hints.hint_db_name
 [@@deriving sexp,yojson,hash,compare]

type 'a hints_path_gen = 'a Hints.hints_path_gen
 [@@deriving sexp,yojson,hash,compare]

type 'a hints_path_atom_gen = 'a Hints.hints_path_atom_gen
 [@@deriving sexp,yojson,hash,compare]

type hints_path = Hints.hints_path
 [@@deriving sexp,yojson,hash,compare]

type 'a hints_transparency_target = 'a Hints.hints_transparency_target [@@deriving sexp,yojson,hash,compare]
type hint_mode = Hints.hint_mode [@@deriving sexp,yojson,hash,compare]
