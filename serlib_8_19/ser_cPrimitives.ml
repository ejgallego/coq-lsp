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

(* open Sexplib *)
(* open Sexplib.Std *)
(* open Ppx_hash_lib.Std.Hash.Builtin *)
(* open Ppx_compare_lib.Builtin *)

module UVars = Ser_uvars

type t =
  [%import: CPrimitives.t]
  [@@deriving sexp,yojson,hash,compare]

type const =
  [%import: CPrimitives.const]
  [@@deriving sexp,yojson,hash,compare]

(* GADTs ... *)
module PTP = struct

  type 'a t = 'a CPrimitives.prim_type

  [@@@ocaml.warning "-27"]

  (* Non-GADT version *)
  type 'a _t =
    | PT_int63
    | PT_float64
    | PT_array
  [@@deriving sexp,yojson,hash,compare]
end

module Prim_type_ = SerType.Pierce1(PTP)
type 'a prim_type = 'a Prim_type_.t
  [@@deriving sexp,yojson,hash,compare]

module OOTP = struct

  type ptype =
    | PT_int63
    | PT_float64
    | PT_array
  [@@deriving sexp,yojson,hash,compare]

  (* op_or_type *)
  type _t =
    | OT_op of t
    | OT_type of ptype
    | OT_const of const
  [@@deriving sexp,yojson,hash,compare]

  type t = CPrimitives.op_or_type
end

module Op_or_type_ = SerType.Pierce(OOTP)
type op_or_type = Op_or_type_.t
  [@@deriving sexp,yojson,hash,compare]
