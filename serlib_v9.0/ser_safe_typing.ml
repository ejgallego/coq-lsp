(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* SerAPI: Coq interaction protocol with bidirectional serialization    *)
(************************************************************************)
(* Copyright 2016-2019 MINES ParisTech -- License LGPL 2.1+             *)
(* Copyright 2019-2023 Inria           -- License LGPL 2.1+             *)
(* Written by: Emilio J. Gallego Arias and others                       *)
(************************************************************************)

open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin
open Sexplib.Std

module ONames = Names
module CEphemeron = Ser_cEphemeron
module Names = Ser_names
module Constr  = Ser_constr
module Declarations = Ser_declarations
module Entries = Ser_entries
module Cooking = Ser_cooking
module Univ = Ser_univ
module Vmemitcodes = Ser_vmemitcodes

(* Side_effects *)
type certificate = {
  certif_struc : Declarations.structure_body;
  certif_univs : Univ.ContextSet.t;
} [@@deriving sexp,yojson,hash,compare]

type side_effect = {
  seff_certif : certificate CEphemeron.key;
  seff_constant : Names.Constant.t;
  seff_body : (Constr.t, Vmemitcodes.body_code option) Declarations.pconstant_body;
  seff_univs : Univ.ContextSet.t;
} [@@deriving sexp,yojson,hash,compare]

module SeffOrd = struct
  type t = side_effect
  [@@deriving sexp,yojson,hash,compare]
end

module SeffSet = Set.Make(SeffOrd)
module SerSeffSet = Ser_cSet.Make(SeffSet)(SeffOrd)

module PC = struct
  (* t  private_constants *)
  type t = Safe_typing.private_constants
  type _t = { seff : side_effect list; elts : SerSeffSet.t }
  [@@deriving sexp,yojson,hash,compare]
end

module B_ = SerType.Pierce(PC)
type private_constants = B_.t
 [@@deriving sexp,yojson,hash,compare]

(*
type 'a effect_entry =
  [%import: 'a Safe_typing.effect_entry]
  [@@deriving sexp_of]

(* XXX: Typical GADT Problem *)
let _effect_entry_of_sexp (_f : Sexp.t -> 'a) (x : Sexp.t) : 'a effect_entry =
  let open Sexp in
  match x with
  | Atom "PureEntry" ->
    Obj__magic PureEntry
  | Atom "EffectEntry" ->
    Obj__magic EffectEntry
  | _ ->
    Sexplib.Conv_error.no_variant_match ()
*)
