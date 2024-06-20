(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(************************************************************************)
(* Status: Very Experimental                                            *)
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

