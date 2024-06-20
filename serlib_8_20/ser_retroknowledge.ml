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

type retroknowledge =
  [%import: Retroknowledge.retroknowledge]

let sexp_of_retroknowledge = Serlib_base.sexp_of_opaque ~typ:"Retroknowledge.retroknowledge"
let retroknowledge_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Retroknowledge.retroknowledge"

(* type entry = 
 *   [%import: Retroknowledge.entry] *)

type action = 
  [%import: Retroknowledge.action]

let sexp_of_action = Serlib_base.sexp_of_opaque ~typ:"Retroknowledge.action"
let action_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Retroknowledge.action"
