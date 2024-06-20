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

open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin
open Sexplib.Std

type level =
  [%import: Conv_oracle.level]
  [@@deriving sexp,yojson,hash,compare]

module OpaqueOracle = struct
  type t = Conv_oracle.oracle
  let name = "Conv_oracle.oracle"
end

module B = SerType.Opaque(OpaqueOracle)
type oracle = B.t
 [@@deriving sexp,yojson,hash,compare]
