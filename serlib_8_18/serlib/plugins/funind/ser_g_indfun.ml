open Serlib

open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin
open Sexplib.Conv

module CAst       = Ser_cAst
module Names      = Ser_names
module Sorts      = Ser_sorts
module Libnames   = Ser_libnames
module Constrexpr = Ser_constrexpr
module Tactypes   = Ser_tactypes
module Genintern  = Ser_genintern
module EConstr    = Ser_eConstr
module Tacexpr    = Serlib_ltac.Ser_tacexpr

module A1 = struct

type h1 = Constrexpr.constr_expr Tactypes.intro_pattern_expr CAst.t option
[@@deriving sexp,hash,compare]
type h2 = Genintern.glob_constr_and_expr Tactypes.intro_pattern_expr CAst.t option
[@@deriving sexp,hash,compare]
type h3 = Tacexpr.intro_pattern option
[@@deriving sexp,hash,compare]

end

let ser_wit_with_names =
  let open A1 in
  Ser_genarg.{
    raw_ser = sexp_of_h1
  ; raw_des = h1_of_sexp
  ; raw_hash = hash_fold_h1
  ; raw_compare = compare_h1

  ; glb_ser = sexp_of_h2
  ; glb_des = h2_of_sexp
  ; glb_hash = hash_fold_h2
  ; glb_compare = compare_h2

  ; top_ser = sexp_of_h3
  ; top_des = h3_of_sexp
  ; top_hash = hash_fold_h3
  ; top_compare = compare_h3
  }

module WitFI = struct
  type raw = Constrexpr.constr_expr Tactypes.with_bindings option
  [@@deriving sexp,hash,compare]
  type glb = Genintern.glob_constr_and_expr Tactypes.with_bindings option
  [@@deriving sexp,hash,compare]
  type top = EConstr.t Tactypes.with_bindings Ser_tactypes.delayed_open option
  [@@deriving sexp,hash,compare]
end

let ser_wit_fun_ind_using = let module M = Ser_genarg.GS(WitFI) in M.genser

module WitFS = struct
  type raw = Names.variable * Libnames.qualid * Sorts.family
  [@@deriving sexp,hash,compare]
  type glb = unit
  [@@deriving sexp,hash,compare]
  type top = unit
  [@@deriving sexp,hash,compare]
end

let ser_wit_fun_scheme_arg = let module M = Ser_genarg.GS(WitFS) in M.genser

module Loc = Ser_loc
module Vernacexpr = Ser_vernacexpr

module WFFD = struct
  type t = Vernacexpr.fixpoint_expr Loc.located
  [@@deriving sexp,hash,compare]
end

let ser_wit_function_fix_definition =
  let module M = Ser_genarg.GS0(WFFD) in M.genser

module WAU = struct
  type raw = Constrexpr.constr_expr list
  [@@deriving sexp,hash,compare]
  type glb = Genintern.glob_constr_and_expr list
  [@@deriving sexp,hash,compare]
  type top = EConstr.constr list
  [@@deriving sexp,hash,compare]
end

let ser_wit_auto_using' = let module M = Ser_genarg.GS(WAU) in M.genser

let register () =
  Ser_genarg.register_genser Funind_plugin.G_indfun.wit_auto_using' ser_wit_auto_using';
  Ser_genarg.register_genser Funind_plugin.G_indfun.wit_constr_comma_sequence' ser_wit_auto_using';
  Ser_genarg.register_genser Funind_plugin.G_indfun.wit_with_names ser_wit_with_names;
  Ser_genarg.register_genser Funind_plugin.G_indfun.wit_fun_ind_using ser_wit_fun_ind_using;
  Ser_genarg.register_genser Funind_plugin.G_indfun.wit_fun_scheme_arg ser_wit_fun_scheme_arg;
  Ser_genarg.register_genser Funind_plugin.G_indfun.wit_function_fix_definition ser_wit_function_fix_definition;
  ()

let _ = register ()
