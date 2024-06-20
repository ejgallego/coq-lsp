(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

open Serlib

open Sexplib.Conv
open Ppx_compare_lib.Builtin
open Ppx_hash_lib.Std.Hash.Builtin

module Loc = Ser_loc
module Names = Ser_names
module Libnames = Ser_libnames
module Locus = Ser_locus
(* module Globnames = Ser_globnames *)

type h1 = Libnames.qualid list
  [@@deriving sexp, hash, compare]

type h2 = Names.GlobRef.t Loc.located Locus.or_var list
[@@deriving sexp, hash, compare]

type h3 = Names.GlobRef.t list
[@@deriving sexp,hash,compare]

let ser_wit_firstorder_using :
  (Libnames.qualid list,
   Names.GlobRef.t Loc.located Locus.or_var list,
   Names.GlobRef.t list) Ser_genarg.gen_ser =
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

let register () =
  Ser_genarg.register_genser Firstorder_plugin.G_ground.wit_firstorder_using ser_wit_firstorder_using;
  ()

let _ = register ()
