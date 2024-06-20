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
(* Copyright 2016-2019 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

type body_code = Vmemitcodes.body_code
 [@@deriving sexp,yojson,hash,compare]

(* type to_patch_substituted = Vmemitcodes.to_patch_substituted
 *
 * val sexp_of_to_patch_substituted : to_patch_substituted -> Sexp.t
 * val to_patch_substituted_of_sexp : Sexp.t -> to_patch_substituted *)
