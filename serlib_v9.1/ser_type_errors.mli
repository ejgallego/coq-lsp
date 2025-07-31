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

type guard_error = Type_errors.guard_error
val guard_error_of_sexp : Sexp.t -> guard_error
val sexp_of_guard_error : guard_error -> Sexp.t

type ('c,'t) pcant_apply_bad_type = ('c, 't) Type_errors.pcant_apply_bad_type

val pcant_apply_bad_type_of_sexp :
  (Sexp.t -> 'constr) -> (Sexp.t -> 'types) ->
  Sexp.t -> ('constr, 'types) pcant_apply_bad_type

val sexp_of_pcant_apply_bad_type :
  ('constr -> Sexp.t) ->
  ('types -> Sexp.t) ->
  ('constr, 'types) pcant_apply_bad_type -> Sexp.t

type ('c, 't, 'r) ptype_error  = ('c, 't, 'r) Type_errors.ptype_error
val ptype_error_of_sexp :
  (Sexp.t -> 'constr) -> (Sexp.t -> 'types) -> (Sexp.t -> 'r) ->
  Sexp.t -> ('constr, 'types, 'r) ptype_error

val sexp_of_ptype_error :
  ('constr -> Sexp.t) ->
  ('types -> Sexp.t) ->
  ('r -> Sexp.t) ->
  ('constr, 'types, 'r) ptype_error -> Sexp.t

type type_error  = Type_errors.type_error
val type_error_of_sexp : Sexp.t -> type_error
val sexp_of_type_error : type_error -> Sexp.t

