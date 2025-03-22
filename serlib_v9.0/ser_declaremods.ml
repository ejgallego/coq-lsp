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

open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin
open Sexplib.Conv

module Nametab = Ser_nametab
module Libobject = Ser_libobject

type 'a module_signature =
  [%import: 'a Declaremods.module_signature]
  [@@deriving sexp,yojson,hash,compare]

type inline =
  [%import: Declaremods.inline]
  [@@deriving sexp,yojson,hash,compare]

type _module_objects =
  { module_prefix : Nametab.object_prefix;
    module_substituted_objects : Libobject.t list;
    module_keep_objects : Libobject.t list;
  } [@@deriving sexp]

