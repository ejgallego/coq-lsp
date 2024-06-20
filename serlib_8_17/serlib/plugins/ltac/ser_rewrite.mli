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

type unary_strategy = Rewrite.unary_strategy
  [@@deriving sexp, hash, compare]

type binary_strategy = Rewrite.binary_strategy
  [@@deriving sexp, hash, compare]

type ('a,'b) strategy_ast = ('a,'b) Rewrite.strategy_ast
  [@@deriving sexp, hash, compare]

type strategy = Rewrite.strategy
  [@@deriving sexp, hash, compare]
