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
(* Status: Experimental                                                 *)
(************************************************************************)

open Sexplib.Std

module Stdlib = Ser_stdlib
module Sorts = Ser_sorts
module Univ = Ser_univ
module Pp = Ser_pp

module Bound = struct
  type t = [%import: UGraph.Bound.t]
  [@@deriving sexp]
end

type t = [%import: UGraph.t]

let sexp_of_t = Serlib_base.sexp_of_opaque ~typ:"UGraph.t"
let t_of_sexp = Serlib_base.opaque_of_sexp ~typ:"UGraph.t"

type path_explanation = [%import: UGraph.path_explanation]

let sexp_of_path_explanation = Serlib_base.sexp_of_opaque ~typ:"UGraph.path_explanation"
let path_explanation_of_sexp = Serlib_base.opaque_of_sexp ~typ:"UGraph.path_explanation"

type explanation = [%import: UGraph.explanation]
  [@@deriving sexp]

type univ_inconsistency =
  [%import: UGraph.univ_inconsistency]
  [@@deriving sexp]
