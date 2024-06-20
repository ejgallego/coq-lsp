open Serlib
open Ltac2_plugin

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Util = Ser_util
module Loc = Ser_loc
module CAst = Ser_cAst
module Names = Ser_names
module Tac2expr = Ser_tac2expr

module WL2 = struct
  type raw = Tac2expr.uid CAst.t list * Tac2expr.raw_tacexpr
  [@@deriving sexp,hash,compare]
  type glb = Tac2expr.uid list * Tac2expr.glb_tacexpr
  [@@deriving sexp,hash,compare]
  type top = Util.Empty.t
  [@@deriving sexp,hash,compare]
end

let ser_wit_ltac2 = let module M = Ser_genarg.GS(WL2) in M.genser

module WLC2 = struct
  type raw = Tac2expr.raw_tacexpr
  [@@deriving sexp,hash,compare]
  type glb = Names.Id.Set.t * Tac2expr.glb_tacexpr
  [@@deriving sexp,hash,compare]
  type top = Util.Empty.t
  [@@deriving sexp,hash,compare]
end

let ser_wit_ltac2_constr = let module M = Ser_genarg.GS(WLC2) in M.genser

module WLQ2 = struct
  type raw = Tac2expr.uid Loc.located
  [@@deriving sexp,hash,compare]
  type glb = Tac2expr.uid
  [@@deriving sexp,hash,compare]
  type top = Util.Empty.t
  [@@deriving sexp,hash,compare]
end

let ser_wit_ltac2_quotation = let module M = Ser_genarg.GS(WLQ2) in M.genser

module WLV2 = struct
  type raw = Util.Empty.t
  [@@deriving sexp,hash,compare]
  type glb = unit
  [@@deriving sexp,hash,compare]
  type top = Util.Empty.t
  [@@deriving sexp,hash,compare]
end

let ser_wit_ltac2_val = let module M = Ser_genarg.GS(WLV2) in M.genser

let register () =
  Ser_genarg.register_genser Tac2env.wit_ltac2 ser_wit_ltac2;
  Ser_genarg.register_genser Tac2env.wit_ltac2_constr ser_wit_ltac2_constr;
  Ser_genarg.register_genser Tac2env.wit_ltac2_quotation ser_wit_ltac2_quotation;
  Ser_genarg.register_genser Tac2env.wit_ltac2_val ser_wit_ltac2_val;
  ()

let () = register ()
