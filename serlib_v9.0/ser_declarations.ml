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

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin
let hash_fold_array = hash_fold_array_frozen

module Rtree   = Ser_rtree
module Names   = Ser_names
module Context = Ser_context
module Constr  = Ser_constr
module Sorts   = Ser_sorts
module Univ    = Ser_univ
module UVars   = Ser_uvars
module CPrimitives = Ser_cPrimitives
module Vmvalues    = Ser_vmvalues
module Conv_oracle = Ser_conv_oracle
module Mod_subst   = Ser_mod_subst
module Opaqueproof = Ser_opaqueproof
module Vmemitcodes = Ser_vmemitcodes
module Retroknowledge = Ser_retroknowledge
module Uint63  = Ser_uint63
module Float64 = Ser_float64
module Pstring = Ser_pstring
module Vmlibrary = Ser_vmlibrary

type template_arity =
  [%import: Declarations.template_arity]
  [@@deriving sexp,yojson,hash,compare]

type ('a, 'b) declaration_arity =
  [%import: ('a, 'b) Declarations.declaration_arity]
  [@@deriving sexp,yojson,hash,compare]

type recarg_type =
  [%import: Declarations.recarg_type]
  [@@deriving sexp,yojson,hash,compare]

type recarg =
  [%import: Declarations.recarg]
  [@@deriving sexp,yojson,hash,compare]

type wf_paths =
  [%import: Declarations.wf_paths]
  [@@deriving sexp,yojson,hash,compare]

type regular_inductive_arity =
  [%import: Declarations.regular_inductive_arity
  [@with Term.sorts := Sorts.t;]]
  [@@deriving sexp,yojson,hash,compare]

type inductive_arity =
  [%import: Declarations.inductive_arity]
  [@@deriving sexp,yojson,hash,compare]

type squash_info =
  [%import: Declarations.squash_info]
  [@@deriving sexp,yojson,hash,compare]

type one_inductive_body =
  [%import: Declarations.one_inductive_body]
  [@@deriving sexp,yojson,hash,compare]

(* type set_predicativity =
 *   [%import: Declarations.set_predicativity]
 *   [@@deriving sexp] *)

(* type engagement =
 *   [%import: Declarations.engagement]
 *   [@@deriving sexp] *)

type inline =
  [%import: Declarations.inline]
  [@@deriving sexp,yojson,hash,compare]

type universes =
  [%import: Declarations.universes]
  [@@deriving sexp,yojson,hash,compare]

type ('a, 'b, 'c) constant_def =
  [%import: ('a, 'b, 'c) Declarations.constant_def]
  [@@deriving sexp,yojson,hash,compare]

type typing_flags =
  [%import: Declarations.typing_flags]
  [@@deriving sexp,yojson,hash,compare]

(* type work_list =
 *   [%import: Declarations.work_list]
 *   [@@deriving sexp] *)

(* type abstr_info =
 *   [%import: Declarations.abstr_info]
 *   [@@deriving sexp] *)

(* type cooking_info =
 *   [%import: Declarations.cooking_info]
 *   [@@deriving sexp] *)

type ('a, 'b) pconstant_body =
  [%import: ('a, 'b) Declarations.pconstant_body]
  [@@deriving sexp,yojson,hash,compare]

type constant_body =
  [%import: Declarations.constant_body]
  [@@deriving sexp,yojson,hash,compare]

let sexp_of_constant_body e =
  (* We cannot handle VM values *)
  sexp_of_constant_body { e with const_body_code = None }

(*
module Retroknowledge =
struct
module MRK = struct
  type t = Retroknowledge.action
  let name = "Retroknowledge.action"
end

module B_ = SerType.Opaque(MRK)
type action = B_.t
  [@@deriving sexp,yojson,hash,compare]
end
*)

type recursivity_kind =
  [%import: Declarations.recursivity_kind]
  [@@deriving sexp,yojson,hash,compare]

type record_info =
  [%import: Declarations.record_info]
  [@@deriving sexp,yojson,hash,compare]

type template_universes =
  [%import: Declarations.template_universes]
  [@@deriving sexp,yojson,hash,compare]

type mutual_inductive_body =
  [%import: Declarations.mutual_inductive_body
  [@with Context.section_context := Context.Named.t;]]
  [@@deriving sexp,yojson,hash,compare]

type instance_mask =
  [%import: UVars.Instance.mask]
  [@@deriving sexp,yojson,hash,compare]

type 'a head_pattern =
  [%import: 'a Declarations.head_pattern
    [@with sort_pattern := Sorts.pattern]]
  [@@deriving sexp,yojson,hash,compare]

type pattern_elimination =
  [%import: Declarations.pattern_elimination]
  [@@deriving sexp,yojson,hash,compare]

and head_elimination =
  [%import: Declarations.head_elimination]
  [@@deriving sexp,yojson,hash,compare]

and pattern_argument =
  [%import: Declarations.pattern_argument]
  [@@deriving sexp,yojson,hash,compare]

type rewrite_rule =
  [%import: Declarations.rewrite_rule]
  [@@deriving sexp,yojson,hash,compare]

type rewrite_rules_body =
  [%import: Declarations.rewrite_rules_body]
  [@@deriving sexp,yojson,hash,compare]

type ('ty,'a) functorize =
  [%import: ('ty, 'a) Declarations.functorize]
  [@@deriving sexp,yojson,hash,compare]

type 'a with_declaration =
  [%import: 'a Declarations.with_declaration]
  [@@deriving sexp,yojson,hash,compare]

type mod_body =
  [%import: Declarations.mod_body]
  [@@deriving sexp,yojson,hash,compare]

type mod_type =
  [%import: Declarations.mod_type]
  [@@deriving sexp,yojson,hash,compare]

module WMBBiject = struct
  type ('a, 'b) t = ('a, 'b) Declarations.when_mod_body

  [@@@ocaml.warning "-27"]
  type ('a, 'b) _t = 'b option
    [@@deriving sexp,yojson,hash,compare]
  [@@@ocaml.warning "+27"]

  let to_t (type a b) (x : b option) : (a, b) Declarations.when_mod_body = match x with
  | Some x -> Obj.magic @@ Declarations.ModBodyVal x
  | None -> Obj.magic @@ Declarations.ModTypeNul

  let of_t (type a) (type b) (x : (a, b) Declarations.when_mod_body) : b option = match x with
  | Declarations.ModBodyVal x -> Some x
  | Declarations.ModTypeNul -> None
end

module WMB = SerType.Biject2(WMBBiject)

 type ('a, 'b) when_mod_body = ('a, 'b) WMB.t
  [@@deriving sexp,yojson,hash,compare]

type 'a module_alg_expr =
  [%import: 'a Declarations.module_alg_expr]
  [@@deriving sexp,yojson,hash,compare]

type 'a functor_alg_expr =
  [%import: 'a Declarations.functor_alg_expr]
  [@@deriving sexp,yojson,hash,compare]

type structure_field_body =
  [%import: Declarations.structure_field_body]
  [@@deriving sexp,yojson,hash,compare]

and structure_body =
  [%import: Declarations.structure_body]
  [@@deriving sexp,yojson,hash,compare]

and module_signature =
  [%import: Declarations.module_signature]
  [@@deriving sexp,yojson,hash,compare]

and module_expression =
  [%import: Declarations.module_expression]
  [@@deriving sexp,yojson,hash,compare]

and module_implementation =
  [%import: Declarations.module_implementation]
  [@@deriving sexp,yojson,hash,compare]

and 'a generic_module_body =
  [%import: 'a Declarations.generic_module_body]
  [@@deriving sexp,yojson,hash,compare]

and module_body =
  [%import: Declarations.module_body]
  [@@deriving sexp,yojson,hash,compare]

and module_type_body =
  [%import: Declarations.module_type_body]
  [@@deriving sexp,yojson,hash,compare]
