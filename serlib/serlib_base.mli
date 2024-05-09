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

(** Controls when an opaque type produces and error vs an "abstract"
   constructor *)
val exn_on_opaque : bool ref

val sexp_of_opaque : typ:string -> 'a -> Sexp.t
val opaque_of_sexp : typ:string -> Sexp.t -> 'a

val opaque_of_yojson : typ:string -> Yojson.Safe.t -> ('a, string) Result.t
val opaque_to_yojson : typ:string -> 'a -> Yojson.Safe.t

val hash_opaque : typ:string -> 'a -> Ppx_hash_lib.Std.Hash.hash_value
val hash_fold_opaque : typ:string -> Ppx_hash_lib.Std.Hash.state -> 'a -> Ppx_hash_lib.Std.Hash.state

val compare_opaque : typ:string -> 'a -> 'a -> int
