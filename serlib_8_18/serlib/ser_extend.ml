(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin
open Sexplib.Std

module Tok           = Ser_tok
module Notation_term = Ser_notation_term
module Constrexpr    = Ser_constrexpr
module Gramlib       = Ser_gramlib

type production_position =
  [%import: Extend.production_position]
  [@@deriving sexp,yojson,hash,compare]

type production_level =
  [%import: Extend.production_level]
  [@@deriving sexp,yojson,hash,compare]

type binder_entry_kind =
  [%import: Extend.binder_entry_kind]
  [@@deriving sexp]

and constr_prod_entry_key =
  [%import: Extend.constr_prod_entry_key]
  [@@deriving sexp]

type 'lev constr_entry_key_gen =
  [%import: 'lev Extend.constr_entry_key_gen]
  [@@deriving sexp,yojson,hash,compare]

type constr_entry_key =
  [%import: Extend.constr_entry_key]
  [@@deriving sexp,yojson,hash,compare]

type simple_constr_prod_entry_key =
  [%import: Extend.simple_constr_prod_entry_key]
  [@@deriving sexp,yojson,hash,compare]

