(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2020 MINES ParisTech / Inria                          *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Ppx_hash_lib.Std
open Ppx_compare_lib.Builtin
open Sexplib.Conv
open Hash.Builtin

module Constrexpr = Ser_constrexpr

type level =
  [%import: Notationextern.level]
  [@@deriving sexp,yojson,hash,compare]

type notation_use =
  [%import: Notationextern.notation_use]
  [@@deriving sexp,yojson,hash,compare]
