(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2020 MINES ParisTech / INRIA                          *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

type definition_object_kind =
  [%import: Decls.definition_object_kind]
  [@@deriving sexp,yojson,hash,compare]

type theorem_kind =
  [%import: Decls.theorem_kind]
  [@@deriving sexp,yojson,hash,compare]

type assumption_object_kind =
  [%import: Decls.assumption_object_kind]
  [@@deriving sexp,yojson,hash,compare]

type logical_kind =
  [%import: Decls.logical_kind]
  [@@deriving sexp,yojson,hash,compare]
