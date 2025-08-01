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

type argument_position = Impargs.argument_position

val argument_position_of_sexp : Sexp.t -> argument_position
val sexp_of_argument_position : argument_position -> Sexp.t

type implicit_explanation = Impargs.implicit_explanation

val implicit_explanation_of_sexp : Sexp.t -> implicit_explanation
val sexp_of_implicit_explanation : implicit_explanation -> Sexp.t

type maximal_insertion = Impargs.maximal_insertion

val maximal_insertion_of_sexp : Sexp.t -> maximal_insertion
val sexp_of_maximal_insertion : maximal_insertion -> Sexp.t

type force_inference = Impargs.force_inference

val force_inference_of_sexp : Sexp.t -> force_inference
val sexp_of_force_inference : force_inference -> Sexp.t

type implicit_side_condition = Impargs.implicit_side_condition
  [@@deriving sexp,yojson,hash,compare]

type implicit_status = Impargs.implicit_status

val implicit_status_of_sexp : Sexp.t -> implicit_status
val sexp_of_implicit_status : implicit_status -> Sexp.t

type implicits_list = Impargs.implicits_list

val implicits_list_of_sexp : Sexp.t -> implicits_list
val sexp_of_implicits_list : implicits_list -> Sexp.t
