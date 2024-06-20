(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
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
