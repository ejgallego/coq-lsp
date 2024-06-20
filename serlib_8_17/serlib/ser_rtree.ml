(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

let hash_fold_array = hash_fold_array_frozen

module RTreePierce = struct

  type 'a t = 'a Rtree.t
  type 'a _t =
    | Param of int * int
    | Node of 'a * 'a _t array
    | Rec of int * 'a _t array
  [@@deriving sexp,yojson,hash,compare]
end

include SerType.Pierce1(RTreePierce)
