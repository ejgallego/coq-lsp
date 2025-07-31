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

let ee = Environ.empty_env

open Sexplib.Std

module Names = Ser_names

module Term        = Ser_constr
module Evd         = Ser_evd
module Evar        = Ser_evar
module Environ     = Ser_environ
module EConstr     = Ser_eConstr
module Univ        = Ser_univ
module UGraph      = Ser_uGraph
module Type_errors = Ser_type_errors
module Locus       = Ser_locus
module Evar_kinds  = Ser_evar_kinds

type unification_error =
  [%import: Pretype_errors.unification_error]
  [@@deriving sexp]

(* workaround env being embedded in the exn, see bug #250 *)
let rec filter_ue (ue : unification_error) = match ue with
  | NotClean (e, _, c) ->
    NotClean (e, ee, c)
  | ConversionFailed (_, c1, c2) ->
    ConversionFailed (ee, c1, c2)
  | IncompatibleInstances (_, e, c1, c2) ->
    IncompatibleInstances (ee, e, c1, c2)
  | InstanceNotSameType (e, _, t1, t2) ->
    InstanceNotSameType (e, ee, t1, t2)
  | CannotSolveConstraint (e, ue) ->
    CannotSolveConstraint (e, (filter_ue ue))
  | ue -> ue

let sexp_of_unification_error ue =
  filter_ue ue |> sexp_of_unification_error

type position =
  [%import: Pretype_errors.position]
  [@@deriving sexp]

type position_reporting =
  [%import: Pretype_errors.position_reporting]
  [@@deriving sexp]

type subterm_unification_error =
  [%import: Pretype_errors.subterm_unification_error]
  [@@deriving sexp]

type type_error =
  [%import: Pretype_errors.type_error]
  [@@deriving sexp]

type pretype_error =
  [%import: Pretype_errors.pretype_error]
  [@@deriving sexp]
