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

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

type source =
  [%import: Loc.source]
  [@@deriving sexp,yojson,hash,compare]

type t =
  [%import: Loc.t]
  [@@deriving sexp,yojson,hash,compare]

let omit_loc = ref false
let sexp_of_t x =
  if !omit_loc then Sexplib.Sexp.Atom "[LOC]" else sexp_of_t x

(* located: public *)
type 'a located = (t option [@ignore]) * 'a
  [@@deriving sexp,yojson,hash,compare]
