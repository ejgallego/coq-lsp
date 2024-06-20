(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

type delta_resolver = Mod_subst.delta_resolver
 [@@deriving sexp,yojson,hash,compare]

type substitution = Mod_subst.substitution
 [@@deriving sexp,yojson,hash,compare]

(* type 'a substituted = 'a Mod_subst.substituted
 * val sexp_of_substituted : ('a -> Sexp.t) -> 'a substituted -> Sexp.t
 * val substituted_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a substituted *)
