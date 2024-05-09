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
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

module Future = Ser_future
module Names  = Ser_names
module Univ   = Ser_univ
module Constr = Ser_constr
module Mod_subst = Ser_mod_subst
module Cooking = Ser_cooking

module OP = struct
type t = [%import: Opaqueproof.opaque]
type _t =
  | Indirect of Mod_subst.substitution list * Cooking.cooking_info list * Names.DirPath.t * int (* subst, discharge, lib, index *)
 [@@deriving sexp,yojson,hash,compare]
end

module B_ = SerType.Pierce(OP)
type opaque = B_.t
 [@@deriving sexp,yojson,hash,compare]

module Map = Ser_cMap.Make(Int.Map)(Ser_int)

module OTSpec = struct
  type t = Opaqueproof.opaquetab
  type _t = {
    opaque_len : int;
    opaque_dir : Names.DirPath.t;
  } [@@deriving sexp,yojson,hash,compare]
end

module C_ = SerType.Pierce(OTSpec)
type opaquetab = C_.t
 [@@deriving sexp,yojson,hash,compare]
