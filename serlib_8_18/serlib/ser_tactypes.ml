(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Conv
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

module CAst        = Ser_cAst
module Names       = Ser_names
module Namegen     = Ser_namegen
module EConstr     = Ser_eConstr

type 'a intro_pattern_action_expr =
  [%import: 'a Tactypes.intro_pattern_action_expr]
and 'a intro_pattern_expr =
  [%import: 'a Tactypes.intro_pattern_expr]
and 'a or_and_intro_pattern_expr =
  [%import: 'a Tactypes.or_and_intro_pattern_expr]
  [@@deriving sexp,yojson,hash,compare]

type quantified_hypothesis =
  [%import: Tactypes.quantified_hypothesis]
  [@@deriving sexp,yojson,hash,compare]

type 'a explicit_bindings =
  [%import: 'a Tactypes.explicit_bindings]
  [@@deriving sexp,yojson,hash,compare]

type 'a bindings =
  [%import: 'a Tactypes.bindings]
  [@@deriving sexp,yojson,hash,compare]

type 'a with_bindings =
  [%import: 'a Tactypes.with_bindings]
  [@@deriving sexp,yojson,hash,compare]

module DO = struct
  type 'a t = 'a Tactypes.delayed_open
  let name = "Tactypes.delayed.open"
end

module B = SerType.Opaque1(DO)
type 'a delayed_open = 'a B.t
 [@@deriving sexp,yojson,hash,compare]

type delayed_open_constr =
  [%import: Tactypes.delayed_open_constr]
  [@@deriving sexp,yojson,hash,compare]

type delayed_open_constr_with_bindings =
  [%import: Tactypes.delayed_open_constr_with_bindings]
  [@@deriving sexp,yojson,hash,compare]

