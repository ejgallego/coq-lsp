(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

open Serlib
open Ltac2_plugin

module Tac2expr = Ser_tac2expr

(* val Ltac2_plugin.G_ltac2.wit_ltac2_entry:
   (Ltac2_plugin.Tac2expr.strexpr, unit, unit) Genarg.genarg_type *)
module L2Entry = struct
  type t = Tac2expr.strexpr
  [@@deriving sexp,hash,compare]
end

let ser_wit_ltac2_entry = let module M = Ser_genarg.GSV(L2Entry) in M.genser

module L2Expr = struct
  type t = Tac2expr.raw_tacexpr
  [@@deriving sexp,hash,compare]
end

let ser_wit_ltac2_expr = let module M = Ser_genarg.GSV(L2Expr) in M.genser

let register () =
  Ser_genarg.register_genser G_ltac2.wit_ltac2_entry ser_wit_ltac2_entry;
  Ser_genarg.register_genser G_ltac2.wit_ltac2_expr ser_wit_ltac2_expr;
  ()

let () = register ()
