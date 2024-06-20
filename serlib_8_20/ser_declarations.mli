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

open Sexplib

type template_arity = Declarations.template_arity
val template_arity_of_sexp : Sexp.t -> template_arity
val sexp_of_template_arity : template_arity -> Sexp.t

type ('a, 'b) declaration_arity = ('a, 'b) Declarations.declaration_arity

val declaration_arity_of_sexp :
  (Sexp.t -> 'a) ->
  (Sexp.t -> 'b) ->
  Sexp.t -> ('a, 'b) declaration_arity

val sexp_of_declaration_arity :
  ('a -> Sexp.t) ->
  ('b -> Sexp.t) ->
  ('a, 'b) declaration_arity -> Sexp.t

type recarg = Declarations.recarg
  [@@deriving sexp,yojson,hash,compare]

type wf_paths = recarg Rtree.t
  [@@deriving sexp,yojson,hash,compare]

type regular_inductive_arity = Declarations.regular_inductive_arity
  [@@deriving sexp,yojson,hash,compare]

type inductive_arity = Declarations.inductive_arity
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

type rewrite_rule = Declarations.rewrite_rule
  [@@deriving sexp,yojson,hash,compare]

type 'a module_alg_expr = 'a Declarations.module_alg_expr
  [@@deriving sexp,yojson,hash,compare]

type structure_body = Declarations.structure_body
  [@@deriving sexp,yojson,hash,compare]

type module_body = Declarations.module_body
  [@@deriving sexp,yojson,hash,compare]

type module_type_body = Declarations.module_type_body
  [@@deriving sexp,yojson,hash,compare]
