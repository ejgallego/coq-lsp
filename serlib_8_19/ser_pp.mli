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

type t = Pp.t
type doc_view = Pp.doc_view

val t_of_sexp : Sexp.t -> t
val sexp_of_t : t -> Sexp.t
val of_yojson : Yojson.Safe.t -> (t, string) Result.result
val to_yojson : t -> Yojson.Safe.t

val doc_view_of_sexp : Sexp.t -> doc_view
val sexp_of_doc_view : doc_view -> Sexp.t
val doc_view_of_yojson : Yojson.Safe.t -> (doc_view, string) Result.result
val doc_view_to_yojson : doc_view -> Yojson.Safe.t
