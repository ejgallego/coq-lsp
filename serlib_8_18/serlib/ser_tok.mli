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

type t = Tok.t

val t_of_sexp : Sexp.t -> t
val sexp_of_t : t -> Sexp.t

type 'c p = 'c Tok.p
val p_of_sexp : (Sexp.t -> 'c) -> Sexp.t -> 'c p
val sexp_of_p : ('c -> Sexp.t) -> 'c p -> Sexp.t
