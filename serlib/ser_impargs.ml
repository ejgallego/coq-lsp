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

module Names = Ser_names
module Constrexpr = Ser_constrexpr

type argument_position =
  [%import: Impargs.argument_position]
  [@@deriving sexp]

type implicit_explanation =
  [%import: Impargs.implicit_explanation]
  [@@deriving sexp]

type maximal_insertion =
  [%import: Impargs.maximal_insertion]
  [@@deriving sexp]

type force_inference =
  [%import: Impargs.force_inference]
  [@@deriving sexp]

module ISCPierceSpec = struct
  type t = Impargs.implicit_side_condition
  type _t = DefaultImpArgs | LessArgsThan of int
  [@@deriving sexp,yojson,hash,compare]
end

module B_ = SerType.Pierce(ISCPierceSpec)
type implicit_side_condition = B_.t
 [@@deriving sexp,yojson,hash,compare]

type implicit_position =
  [%import: Impargs.implicit_position]
  [@@deriving sexp]

type implicit_status_info =
  [%import: Impargs.implicit_status_info]
  [@@deriving sexp]

type implicit_status =
  [%import: Impargs.implicit_status]
  [@@deriving sexp]

type implicits_list =
  [%import: Impargs.implicits_list]
  [@@deriving sexp]




