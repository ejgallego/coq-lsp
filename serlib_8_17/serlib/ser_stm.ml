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

(* open Sexplib.Conv *)

module Stateid = Ser_stateid
module Names   = Ser_names

(* type interactive_top =
 *  [%import: Stm.interactive_top]
 *  [@@deriving sexp] *)

type focus =
 [%import: Stm.focus]
 [@@deriving sexp]

type add_focus =
 [%import: Stm.add_focus]
 [@@deriving sexp]

 (* { start : Stateid.t; stop : Stateid.t; tip : Stateid.t } *)

