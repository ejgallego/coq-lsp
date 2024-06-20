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

type subscopes = Notation_term.subscopes
  [@@deriving sexp,yojson,hash,compare]

type notation_binder_kind = Notation_term.notation_binder_kind
  [@@deriving sexp,yojson,hash,compare]

type notation_var_internalization_type = Notation_term.notation_var_internalization_type
  [@@deriving sexp,yojson,hash,compare]
