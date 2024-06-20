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

module Variance : SerType.SJHC with type t = UVars.Variance.t

module Instance : SerType.SJHC with type t = UVars.Instance.t

module UContext : SerType.SJHC with type t = UVars.UContext.t

module AbstractContext : SerType.SJHC with type t = UVars.AbstractContext.t

(** A value in a universe context (resp. context set). *)
type 'a in_universe_context = 'a UVars.in_universe_context
val in_universe_context_of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a in_universe_context
val sexp_of_in_universe_context : ('a -> Sexp.t) -> 'a in_universe_context -> Sexp.t

type 'a puniverses = 'a * Instance.t
 [@@deriving sexp,yojson,hash,compare]
