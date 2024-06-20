open Serlib
open Ltac2_plugin

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Tac2expr = Ser_tac2expr

(* val Ltac2_plugin.G_ltac2.wit_ltac2_entry:
   (Ltac2_plugin.Tac2expr.strexpr, unit, unit) Genarg.genarg_type *)
module L2Entry = struct
  type raw = Tac2expr.strexpr
  [@@deriving sexp,hash,compare]
  type glb = unit
  [@@deriving sexp,hash,compare]
  type top = unit
  [@@deriving sexp,hash,compare]
end

let ser_wit_ltac2_entry = let module M = Ser_genarg.GS(L2Entry) in M.genser

module L2Expr = struct
  type raw = Tac2expr.raw_tacexpr
  [@@deriving sexp,hash,compare]
  type glb = unit
  [@@deriving sexp,hash,compare]
  type top = unit
  [@@deriving sexp,hash,compare]
end

let ser_wit_ltac2_expr = let module M = Ser_genarg.GS(L2Expr) in M.genser

let register () =
  Ser_genarg.register_genser G_ltac2.wit_ltac2_entry ser_wit_ltac2_entry;
  Ser_genarg.register_genser G_ltac2.wit_ltac2_expr ser_wit_ltac2_expr;
  ()

let () = register ()
