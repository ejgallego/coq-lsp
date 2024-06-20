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

open Ppx_sexp_conv_lib.Conv
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Univ = Ser_univ

type family =
  [%import: Sorts.family]
  [@@deriving sexp,yojson,hash,compare]

module BijectQVar = struct
  open Sexplib.Std
  open Ppx_hash_lib.Std.Hash.Builtin
  open Ppx_compare_lib.Builtin
  type t = Sorts.QVar.t
  type _t = [%import: Sorts.QVar.repr] [@@deriving sexp,yojson,hash,compare]
  let of_t = Sorts.QVar.repr
  let to_t = Sorts.QVar.of_repr
end

module QVar = struct
  module Self = SerType.Biject(BijectQVar)
  include Self

  module Set = Ser_cSet.Make(Sorts.QVar.Set)(Self)
end

module Quality = struct
  type constant = [%import: Sorts.Quality.constant] [@@deriving sexp,yojson,hash,compare]
  module Self = struct
    type t = [%import: Sorts.Quality.t] [@@deriving sexp,yojson,hash,compare]
  end
  include Self
  module Set = Ser_cSet.Make(Sorts.Quality.Set)(Self)
  type pattern = [%import: Sorts.Quality.pattern] [@@deriving sexp,yojson,hash,compare]
end

module PierceSpec = struct
  type t = Sorts.t
  type _t =
    | SProp
    | Prop
    | Set
    | Type of Univ.Universe.t
    | QSort of QVar.t * Univ.Universe.t
  [@@deriving sexp,yojson,hash,compare]
end

include SerType.Pierce(PierceSpec)

type relevance =
  [%import: Sorts.relevance]
  [@@deriving sexp,yojson,hash,compare]

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

type pattern =
  [%import: Sorts.pattern]
  [@@deriving sexp,yojson,hash,compare]

module QConstraint = struct
  type kind =
    [%import: Sorts.QConstraint.kind]
    [@@deriving sexp,yojson,hash,compare]

  type t =
    [%import: Sorts.QConstraint.t]
    [@@deriving sexp,yojson,hash,compare]
end

module QConstraints = Ser_cSet.Make(Sorts.QConstraints)(QConstraint)
