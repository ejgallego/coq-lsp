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

open Sexplib.Conv
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Sorts = Ser_sorts
module Names = Ser_names
module Univ  = Ser_univ
module Uint63 = Ser_uint63
module Float64 = Ser_float64

type tag =
  [%import: Vmvalues.tag]
  [@@deriving sexp,yojson,hash,compare]

module OpaqueSV = struct
  type t = Vmvalues.structured_values
  let name = "Vmvalues.structured_values"
end

module B = SerType.Opaque(OpaqueSV)

type structured_values = B.t
let sexp_of_structured_values = B.sexp_of_t
let structured_values_of_sexp = B.t_of_sexp
let structured_values_of_yojson = B.of_yojson
let structured_values_to_yojson = B.to_yojson
(* let hash_structured_values = B.hash *)
let hash_fold_structured_values = B.hash_fold_t
let compare_structured_values = B.compare

type structured_constant =
  [%import: Vmvalues.structured_constant]
  [@@deriving sexp,yojson,hash,compare]

let hash_fold_array = hash_fold_array_frozen

type reloc_table =
  [%import: Vmvalues.reloc_table]
  [@@deriving sexp,yojson,hash,compare]

type annot_switch =
  [%import: Vmvalues.annot_switch]
  [@@deriving sexp,yojson,hash,compare]
