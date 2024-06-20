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

module Stdlib = Ser_stdlib
module CEphemeron = Ser_cEphemeron
module Range  = Ser_range
module Names  = Ser_names
module Constr = Ser_constr
module Univ   = Ser_univ
module Sorts  = Ser_sorts
module Nativevalues   = Ser_nativevalues
module Opaqueproof    = Ser_opaqueproof
module Retroknowledge = Ser_retroknowledge
module UGraph         = Ser_uGraph
module Declarations   = Ser_declarations
module Vmlibrary      = Ser_vmlibrary

(* type stratification =
 *   [%import: Environ.stratification]
 *   [@@deriving sexp_of] *)

type rel_context_val =
  [%import: Environ.rel_context_val]
  [@@deriving sexp_of]

type named_context_val =
  [%import: Environ.named_context_val]
  [@@deriving sexp_of]

type link_info =
  [%import: Environ.link_info]
  [@@deriving sexp,yojson,hash,compare]

type key =
  [%import: Environ.key]
  [@@deriving sexp,yojson,hash,compare]

type constant_key =
  [%import: Environ.constant_key]
  [@@deriving sexp,yojson,hash,compare]

type mind_key =
  [%import: Environ.mind_key]
  [@@deriving sexp,yojson,hash,compare]

module Globals = struct

  module PierceSpec = struct
    type t = Environ.Globals.t
    type _t = [%import: Environ.Globals.view]
    [@@deriving sexp,yojson,hash,compare]
  end
  include SerType.Pierce(PierceSpec)
end

type env =
  [%import: Environ.env]
  [@@deriving sexp_of]

let env_of_sexp = Serlib_base.opaque_of_sexp ~typ:"Environ.env"

let abstract_env = ref false
let sexp_of_env env =
  if !abstract_env
  then Serlib_base.sexp_of_opaque ~typ:"Environ.env" env
  else sexp_of_env env

type ('constr, 'term) punsafe_judgment =
  [%import: ('constr, 'term) Environ.punsafe_judgment]
  [@@deriving sexp]

type unsafe_judgment =
  [%import: Environ.unsafe_judgment]
  [@@deriving sexp]
