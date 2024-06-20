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

open Sexplib.Conv
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Stdlib     = Ser_stdlib
module Names      = Ser_names
module Environ    = Ser_environ
module Glob_term  = Ser_glob_term
module Constrexpr = Ser_constrexpr
module Pattern    = Ser_pattern
module Notation_term = Ser_notation_term

module Store = struct

  module StoreOpaque = struct type t = Genintern.Store.t let name = "Genintern.Store.t" end

  include SerType.Opaque(StoreOpaque)

end

type intern_variable_status =
  [%import: Genintern.intern_variable_status]
  [@@deriving sexp,yojson,hash,compare]

type glob_sign =
  [%import: Genintern.glob_sign]
  [@@deriving sexp]

type glob_constr_and_expr =
  [%import: Genintern.glob_constr_and_expr]
  [@@deriving sexp,yojson,hash,compare]

type glob_constr_pattern_and_expr =
  [%import: Genintern.glob_constr_pattern_and_expr]
  [@@deriving sexp,yojson,hash,compare]
