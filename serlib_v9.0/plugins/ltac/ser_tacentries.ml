(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
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

open Serlib

module Loc   = Ser_loc
module Names = Ser_names

open Ltac_plugin [@@ocaml.warning "-33"]

type 'a grammar_tactic_prod_item_expr =
  [%import: 'a Ltac_plugin.Tacentries.grammar_tactic_prod_item_expr]
  [@@deriving sexp,hash,compare]

type raw_argument =
  [%import: Ltac_plugin.Tacentries.raw_argument]
  [@@deriving sexp,hash,compare]
