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

(** Control whether to output environs, they are huge, and in some
   case problematic; if abstract_env is true, they will be serialized
   as abstract *)
val abstract_env : bool ref

type env = Environ.env

val env_of_sexp : Sexp.t -> env val sexp_of_env : env -> Sexp.t

type ('constr, 'types) punsafe_judgment = ('constr, 'types)
   Environ.punsafe_judgment

val punsafe_judgment_of_sexp : (Sexp.t -> 'constr) -> (Sexp.t ->
   'types) -> Sexp.t -> ('constr, 'types) punsafe_judgment val
   sexp_of_punsafe_judgment : ('constr -> Sexplib.Sexp.t) -> ('types
   -> Sexplib.Sexp.t) -> ('constr, 'types) punsafe_judgment -> Sexp.t

type unsafe_judgment = Environ.unsafe_judgment val
   unsafe_judgment_of_sexp : Sexp.t -> unsafe_judgment val
   sexp_of_unsafe_judgment : unsafe_judgment -> Sexp.t
