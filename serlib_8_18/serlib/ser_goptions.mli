(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib

type option_locality = Goptions.option_locality
[@@deriving sexp, yojson, hash,compare]

type option_name = Goptions.option_name
[@@deriving sexp, yojson, hash,compare]

type option_value = Goptions.option_value

val option_value_of_sexp : Sexp.t -> option_value
val sexp_of_option_value : option_value -> Sexp.t
val option_value_of_yojson : Yojson.Safe.t -> (option_value, string) Result.result
val option_value_to_yojson : option_value -> Yojson.Safe.t

type option_state = Goptions.option_state

val option_state_of_sexp : Sexp.t -> option_state
val sexp_of_option_state : option_state -> Sexp.t

type table_value = Goptions.table_value [@@deriving sexp, yojson, hash,compare]
