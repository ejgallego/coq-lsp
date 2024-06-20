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
(* Copyright 2016-2019 MINES ParisTech                                  *)
(* Written byo: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Names = Ser_names
module CPrimitives = Ser_cPrimitives
module Mod_subst = Ser_mod_subst
module Vmvalues = Ser_vmvalues
module Vmbytecodes = Ser_vmbytecodes

type reloc_info =
  | Reloc_annot of Vmvalues.annot_switch
  | Reloc_const of Vmvalues.structured_constant
  | Reloc_getglobal of Names.Constant.t
  | Reloc_caml_prim of CPrimitives.t
 [@@deriving sexp,yojson,hash,compare]

let hash_fold_array = hash_fold_array_frozen

type patches = {
  reloc_infos : (reloc_info * int array) array;
} [@@deriving sexp,yojson,hash,compare]

type emitcodes = string
 [@@deriving sexp,yojson,hash,compare]

type _to_patch = emitcodes * patches
 [@@deriving sexp,yojson,hash,compare]

module PierceToPatch = struct

  type t = Vmemitcodes.to_patch
  type _t = _to_patch
   [@@deriving sexp,yojson,hash,compare]

end

module B = SerType.Pierce(PierceToPatch)
type to_patch = B.t
 [@@deriving sexp,yojson,hash,compare]

type body_code =
  [%import: Vmemitcodes.body_code]
  [@@deriving sexp,yojson,hash,compare]
