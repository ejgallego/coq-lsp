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

module Univ = Ser_univ

type family =
  [%import: Sorts.family]
  [@@deriving sexp,yojson,hash,compare]

module BijectQVar = struct
  open Sexplib.Std
  open Ppx_hash_lib.Std.Hash.Builtin
  open Ppx_compare_lib.Builtin
  type t = Sorts.QVar.t
  type _t = string * int [@@deriving sexp,yojson,hash,compare]
  let of_t = Sorts.QVar.repr
  let to_t (s,i) = Sorts.QVar.make s i
end

module QVar = SerType.Biject(BijectQVar)

module PierceSpec = struct
  type t = Sorts.t
  type _t =
    | SProp
    | Prop
    | Set
    | Type of Univ.Universe.t
    | QSort of QVar.t * Univ.Universe.t
  [@@deriving sexp,yojson,hash,compare]
end

include SerType.Pierce(PierceSpec)

type relevance =
  [%import: Sorts.relevance]
  [@@deriving sexp,yojson,hash,compare]
