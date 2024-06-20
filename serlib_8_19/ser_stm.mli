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

open Sexplib

(* type interactive_top = Stm.interactive_top
 * 
 * val sexp_of_interactive_top : Stm.interactive_top -> Sexp.t
 * val interactive_top_of_sexp : Sexp.t -> Stm.interactive_top *)

type focus = Stm.focus

val sexp_of_focus : Stm.focus -> Sexp.t
val focus_of_sexp : Sexp.t -> Stm.focus

type add_focus = Stm.add_focus

val sexp_of_add_focus : Stm.add_focus -> Sexp.t
val add_focus_of_sexp : Sexp.t -> Stm.add_focus
