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

open Sexplib

(************************************************************************)
(* Evar_kinds.mli                                                       *)
(************************************************************************)
type matching_var_kind = Evar_kinds.matching_var_kind
  [@@deriving sexp,yojson,hash,compare]

type obligation_definition_status = Evar_kinds.obligation_definition_status

val obligation_definition_status_of_sexp : Sexp.t -> obligation_definition_status
val sexp_of_obligation_definition_status : obligation_definition_status -> Sexp.t

include SerType.SJHC with type t = Evar_kinds.t
