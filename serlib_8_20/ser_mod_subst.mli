(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

type delta_resolver = Mod_subst.delta_resolver
 [@@deriving sexp,yojson,hash,compare]

type substitution = Mod_subst.substitution
 [@@deriving sexp,yojson,hash,compare]

(* type 'a substituted = 'a Mod_subst.substituted
 * val sexp_of_substituted : ('a -> Sexp.t) -> 'a substituted -> Sexp.t
 * val substituted_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a substituted *)
