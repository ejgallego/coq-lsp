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

type recarg = Declarations.recarg
  [@@deriving sexp,yojson,hash,compare]

type wf_paths = recarg Rtree.t
  [@@deriving sexp,yojson,hash,compare]

type one_inductive_body = Declarations.one_inductive_body
  [@@deriving sexp,yojson,hash,compare]

(* type set_predicativity = Declarations.set_predicativity
 * val set_predicativity_of_sexp : Sexp.t -> set_predicativity
 * val sexp_of_set_predicativity : set_predicativity -> Sexp.t *)

(* type engagement = Declarations.engagement
 * val engagement_of_sexp : Sexp.t -> engagement
 * val sexp_of_engagement : engagement -> Sexp.t *)

type typing_flags = Declarations.typing_flags
  [@@deriving sexp,yojson,hash,compare]

type inline = Declarations.inline
  [@@deriving sexp,yojson,hash,compare]

(* type work_list = Declarations.work_list *)

(* type abstr_info = Declarations.abstr_info = {
 *   abstr_ctx : Constr.named_context;
 *   abstr_subst : Univ.Instance.t;
 *   abstr_uctx : Univ.AbstractContext.t;
 * }
 * 
 * type cooking_info = Declarations.cooking_info
 * val sexp_of_cooking_info : cooking_info -> Sexp.t
 * val cooking_info_of_sexp : Sexp.t -> cooking_info *)

type ('a, 'b) pconstant_body = ('a, 'b) Declarations.pconstant_body
  [@@deriving sexp,yojson,hash,compare]

type constant_body = Declarations.constant_body
  [@@deriving sexp,yojson,hash,compare]

(* type record_body = Declarations.record_body
 * val record_body_of_sexp : Sexp.t -> record_body
 * val sexp_of_record_body : record_body -> Sexp.t *)

type recursivity_kind = Declarations.recursivity_kind
  [@@deriving sexp,yojson,hash,compare]

type mutual_inductive_body = Declarations.mutual_inductive_body
  [@@deriving sexp,yojson,hash,compare]

type machine_rewrite_rule = Declarations.machine_rewrite_rule
  [@@deriving sexp,yojson,hash,compare]

type mod_body = Declarations.mod_body
type mod_type = Declarations.mod_type

type ('ty, 'a) functorize = ('ty, 'a) Declarations.functorize
  [@@deriving sexp,yojson,hash,compare]

type 'a module_alg_expr = 'a Declarations.module_alg_expr
  [@@deriving sexp,yojson,hash,compare]

type module_expression = Declarations.module_expression
  [@@deriving sexp,yojson,hash,compare]

type ('a, 'b) structure_field_body = ('a, 'b) Declarations.structure_field_body
  [@@deriving sexp,yojson,hash,compare]

type ('a, 'b) structure_body = ('a, 'b) Declarations.structure_body
  [@@deriving sexp,yojson,hash,compare]
