(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin
open Sexplib.Std

module Loc   = Ser_loc
module Names = Ser_names
module Util  = Ser_util
module Locus = Ser_locus
module Libnames = Ser_libnames
module Constrexpr = Ser_constrexpr

type 'a red_atom =
  [%import: 'a Genredexpr.red_atom]
  [@@deriving sexp]

type 'a glob_red_flag =
  [%import: 'a Genredexpr.glob_red_flag]
  [@@deriving sexp,yojson,hash,compare]

type ('a,'b,'c,'d) red_expr_gen0 =
  [%import: ('a,'b,'c,'d) Genredexpr.red_expr_gen0]
  [@@deriving sexp,yojson,hash,compare]

type ('a,'b,'c) red_expr_gen =
  [%import: ('a,'b,'c) Genredexpr.red_expr_gen]
  [@@deriving sexp,yojson,hash,compare]

type ('a,'b,'c) may_eval =
  [%import: ('a,'b,'c) Genredexpr.may_eval]
  [@@deriving sexp,yojson,hash,compare]

(* Helpers for raw_red_expr *)
type r_trm =
  [%import: Genredexpr.r_trm]
  [@@deriving sexp,yojson,hash,compare]

type r_cst =
  [%import: Genredexpr.r_cst]
  [@@deriving sexp,yojson,hash,compare]

type r_pat =
  [%import: Genredexpr.r_pat]
  [@@deriving sexp,yojson,hash,compare]

type raw_red_expr =
  [%import: Genredexpr.raw_red_expr]
  [@@deriving sexp,yojson,hash,compare]

type 'a and_short_name =
  [%import: 'a Genredexpr.and_short_name]
  [@@deriving sexp,yojson,hash,compare]

module A = struct

  type raw =
    (Ser_constrexpr.constr_expr,
     Ser_libnames.qualid Ser_constrexpr.or_by_notation,
     Ser_constrexpr.constr_expr) red_expr_gen
  [@@deriving sexp,yojson,hash,compare]

  type glb =
    (Ser_genintern.glob_constr_and_expr,
     Ser_tacred.evaluable_global_reference and_short_name Ser_locus.or_var,
     Ser_genintern.glob_constr_pattern_and_expr) red_expr_gen
  [@@deriving sexp,yojson,hash,compare]

  type top =
    (Ser_eConstr.constr,
     Ser_tacred.evaluable_global_reference,
     Ser_pattern.constr_pattern) red_expr_gen
  [@@deriving sexp,yojson,hash,compare]
end

let ser_wit_red_expr = let module M = Ser_genarg.GS(A) in M.genser

let register () =
    Ser_genarg.register_genser Redexpr.wit_red_expr ser_wit_red_expr;
    ()

let _ =
  register ()
