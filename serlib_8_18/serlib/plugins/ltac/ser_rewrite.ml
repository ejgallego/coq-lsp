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

open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin
open Sexplib.Conv

type unary_strategy =
  [%import: Rewrite.unary_strategy]
  [@@deriving sexp,hash,compare]

type binary_strategy =
  [%import: Rewrite.binary_strategy]
  [@@deriving sexp,hash,compare]

type nary_strategy =
  [%import: Rewrite.nary_strategy]
  [@@deriving sexp,hash,compare]

type ('a,'b) strategy_ast =
  [%import: ('a,'b) Rewrite.strategy_ast]
  [@@deriving sexp,hash,compare]

type strategy = Rewrite.strategy

let strategy_of_sexp = Serlib.Serlib_base.opaque_of_sexp ~typ:"rewrite/strategy"
let sexp_of_strategy = Serlib.Serlib_base.sexp_of_opaque ~typ:"rewrite/strategy"
let hash_strategy = Hashtbl.hash
let hash_fold_strategy st d = Ppx_hash_lib.Std.Hash.Builtin.hash_fold_int st (Hashtbl.hash d)
let compare_strategy = Stdlib.compare
