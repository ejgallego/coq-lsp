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

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Names = Ser_names
module Constrexpr = Ser_constrexpr

type argument_position =
  [%import: Impargs.argument_position]
  [@@deriving sexp]

type implicit_explanation =
  [%import: Impargs.implicit_explanation]
  [@@deriving sexp]

type maximal_insertion =
  [%import: Impargs.maximal_insertion]
  [@@deriving sexp]

type force_inference =
  [%import: Impargs.force_inference]
  [@@deriving sexp]

module ISCPierceSpec = struct
  type t = Impargs.implicit_side_condition
  type _t = DefaultImpArgs | LessArgsThan of int
  [@@deriving sexp,yojson,hash,compare]
end

module B_ = SerType.Pierce(ISCPierceSpec)
type implicit_side_condition = B_.t
 [@@deriving sexp,yojson,hash,compare]

type implicit_position =
  [%import: Impargs.implicit_position]
  [@@deriving sexp]

type implicit_status =
  [%import: Impargs.implicit_status]
  [@@deriving sexp]

type implicits_list =
  [%import: Impargs.implicits_list]
  [@@deriving sexp]




