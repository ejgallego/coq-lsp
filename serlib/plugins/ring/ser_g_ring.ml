(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

open Sexplib.Conv
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin
open Serlib

module CAst       = Ser_cAst
module Libnames   = Ser_libnames
module Constrexpr = Ser_constrexpr
module Tactypes   = Ser_tactypes
module Genintern  = Ser_genintern
module EConstr    = Ser_eConstr
module Tacexpr    = Serlib_ltac.Ser_tacexpr

module Ltac_plugin = struct
  module Tacexpr = Serlib_ltac.Ser_tacexpr
end

type 'constr coeff_spec =
  [%import: 'constr Ring_plugin.Ring_ast.coeff_spec]
  [@@deriving sexp,hash,compare]

type cst_tac_spec =
  [%import: Ring_plugin.Ring_ast.cst_tac_spec]
  [@@deriving sexp,hash,compare]

type 'constr ring_mod =
  [%import: 'constr Ring_plugin.Ring_ast.ring_mod]
  [@@deriving sexp,hash,compare]

type 'a field_mod =
  [%import: 'a Ring_plugin.Ring_ast.field_mod]
  [@@deriving sexp,hash,compare]

module A0 = struct
  type t = Constrexpr.constr_expr field_mod
    [@@deriving sexp,hash,compare]
end

let ser_wit_field_mod = let module M = Ser_genarg.GSV(A0) in M.genser

module A1 = struct
  type t = Constrexpr.constr_expr field_mod list
    [@@deriving sexp,hash,compare]
end

let ser_wit_field_mods = let module M = Ser_genarg.GSV(A1) in M.genser

module A2 = struct
  type t = Constrexpr.constr_expr ring_mod
    [@@deriving sexp,hash,compare]
end

let ser_wit_ring_mod = let module M = Ser_genarg.GSV(A2) in M.genser

module A3 = struct
  type t = Constrexpr.constr_expr ring_mod list
    [@@deriving sexp,hash,compare]
end

let ser_wit_ring_mods = let module M = Ser_genarg.GSV(A3) in M.genser

let register () =
  Ser_genarg.register_genser Ring_plugin.G_ring.wit_field_mod  ser_wit_field_mod;
  Ser_genarg.register_genser Ring_plugin.G_ring.wit_field_mods ser_wit_field_mods;
  Ser_genarg.register_genser Ring_plugin.G_ring.wit_ring_mod  ser_wit_ring_mod;
  Ser_genarg.register_genser Ring_plugin.G_ring.wit_ring_mods ser_wit_ring_mods;
  ()

let _ = register ()
