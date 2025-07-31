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
open Sexplib.Std

type level =
  [%import: Conv_oracle.level]
  [@@deriving sexp,yojson,hash,compare]

module OpaqueOracle = struct
  type t = Conv_oracle.oracle
  let name = "Conv_oracle.oracle"
end

module B = SerType.Opaque(OpaqueOracle)
type oracle = B.t
 [@@deriving sexp,yojson,hash,compare]
