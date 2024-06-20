(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

type infix_flag =
  [%import: Vernacexpr.infix_flag]
  [@@deriving sexp,yojson,hash,compare]

type opacity_flag =
  [%import: Vernacexpr.opacity_flag]
  [@@deriving sexp,yojson,hash,compare]

type scope_name =
  [%import: Vernacexpr.scope_name]
  [@@deriving sexp,yojson,hash,compare]

type notation_format =
  [%import: Vernacexpr.notation_format]
  [@@deriving sexp,yojson,hash,compare]

type syntax_modifier =
  [%import: Vernacexpr.syntax_modifier]
  [@@deriving sexp,yojson,hash,compare]

type class_rawexpr =
  [%import: Vernacexpr.class_rawexpr]
  [@@deriving sexp,yojson,hash,compare]

type goal_reference =
  [%import: Vernacexpr.goal_reference]
  [@@deriving sexp,yojson,hash,compare]

type printable =
  [%import: Vernacexpr.printable]
  [@@deriving sexp,yojson,hash,compare]

type glob_search_where =
  [%import: Vernacexpr.glob_search_where]
  [@@deriving sexp,yojson,hash,compare]

type search_item =
  [%import: Vernacexpr.search_item]
  [@@deriving sexp,yojson,hash,compare]

type search_request =
  [%import: Vernacexpr.search_request]
  [@@deriving sexp,yojson,hash,compare]

type searchable =
  [%import: Vernacexpr.searchable]
  [@@deriving sexp,yojson,hash,compare]

type locatable =
  [%import: Vernacexpr.locatable]
  [@@deriving sexp,yojson,hash,compare]

type showable =
  [%import: Vernacexpr.showable]
  [@@deriving sexp,yojson,hash,compare]

type comment =
  [%import: Vernacexpr.comment]
  [@@deriving sexp,yojson,hash,compare]

type search_restriction =
  [%import: Vernacexpr.search_restriction]
  [@@deriving sexp,yojson,hash,compare]

type verbose_flag =
  [%import: Vernacexpr.verbose_flag]
  [@@deriving sexp,yojson,hash,compare]

type coercion_flag =
  [%import: Vernacexpr.coercion_flag]
  [@@deriving sexp,yojson,hash,compare]

type instance_flag =
  [%import: Vernacexpr.instance_flag]
  [@@deriving sexp,yojson,hash,compare]

type export_flag =
  [%import: Vernacexpr.export_flag]
  [@@deriving sexp,yojson,hash,compare]

type locality_flag =
  [%import: Vernacexpr.locality_flag]
  [@@deriving sexp,yojson,hash,compare]

type definition_expr =
  [%import: Vernacexpr.definition_expr]
  [@@deriving sexp,yojson,hash,compare]

type decl_notation =
  [%import: Vernacexpr.decl_notation]
  [@@deriving sexp,yojson,hash,compare]

type 'a fix_expr_gen =
  [%import: 'a Vernacexpr.fix_expr_gen]
  [@@deriving sexp,yojson,hash,compare]

type fixpoint_expr =
  [%import: Vernacexpr.fixpoint_expr]
  [@@deriving sexp,yojson,hash,compare]

type cofixpoint_expr =
  [%import: Vernacexpr.cofixpoint_expr]
  [@@deriving sexp,yojson,hash,compare]

type local_decl_expr =
  [%import: Vernacexpr.local_decl_expr]
  [@@deriving sexp,yojson,hash,compare]

type inductive_kind =
  [%import: Vernacexpr.inductive_kind]
  [@@deriving sexp,yojson,hash,compare]

type simple_binder =
  [%import: Vernacexpr.simple_binder]
  [@@deriving sexp,yojson,hash,compare]

type class_binder =
  [%import: Vernacexpr.class_binder]
  [@@deriving sexp,yojson,hash,compare]

type 'a with_coercion =
  [%import: 'a Vernacexpr.with_coercion]
  [@@deriving sexp,yojson,hash,compare]

type 'a with_coercion_instance =
  [%import: 'a Vernacexpr.with_coercion_instance]
  [@@deriving sexp,yojson,hash,compare]

type constructor_expr =
  [%import: Vernacexpr.constructor_expr]
  [@@deriving sexp,yojson,hash,compare]

type record_field_attr =
  [%import: Vernacexpr.record_field_attr]
  [@@deriving sexp,yojson,hash,compare]

type constructor_list_or_record_decl_expr =
  [%import: Vernacexpr.constructor_list_or_record_decl_expr]
  [@@deriving sexp,yojson,hash,compare]

type inductive_params_expr =
  [%import: Vernacexpr.inductive_params_expr]
  [@@deriving sexp,yojson,hash,compare]

type inductive_expr =
  [%import: Vernacexpr.inductive_expr]
  [@@deriving sexp,yojson,hash,compare]

type one_inductive_expr =
  [%import: Vernacexpr.one_inductive_expr]
  [@@deriving sexp,yojson,hash,compare]

type proof_expr =
  [%import: Vernacexpr.proof_expr]
  [@@deriving sexp,yojson,hash,compare]

type proof_end =
  [%import: Vernacexpr.proof_end]
  [@@deriving sexp,yojson,hash,compare]

type scheme_type =
  [%import: Vernacexpr.scheme_type]
  [@@deriving sexp,yojson,hash,compare]

type scheme =
  [%import: Vernacexpr.scheme]
  [@@deriving sexp,yojson,hash,compare]

type section_subset_expr =
  [%import: Vernacexpr.section_subset_expr]
  [@@deriving sexp,yojson,hash,compare]

type extend_name =
  [%import: Vernacexpr.extend_name]
  [@@deriving sexp,yojson,hash,compare]

type register_kind =
  [%import: Vernacexpr.register_kind]
  [@@deriving sexp,yojson,hash,compare]

type module_ast_inl =
  [%import: Vernacexpr.module_ast_inl]
  [@@deriving sexp,yojson,hash,compare]

type discharge =
  [%import: Vernacexpr.discharge]
  [@@deriving sexp,yojson,hash,compare]

type equality_scheme_type =
  [%import: Vernacexpr.equality_scheme_type]
  [@@deriving sexp,yojson,hash,compare]

type import_categories =
  [%import: Vernacexpr.import_categories]
  [@@deriving sexp,yojson,hash,compare]

type export_with_cats =
  [%import: Vernacexpr.export_with_cats]
  [@@deriving sexp,yojson,hash,compare]

type module_binder =
  [%import: Vernacexpr.module_binder]
  [@@deriving sexp,yojson,hash,compare]

type one_import_filter_name =
  [%import: Vernacexpr.one_import_filter_name]
  [@@deriving sexp,yojson,hash,compare]

type import_filter_expr =
  [%import: Vernacexpr.import_filter_expr]
  [@@deriving sexp,yojson,hash,compare]

type hint_info_expr =
  [%import: Vernacexpr.hint_info_expr]
  [@@deriving sexp,yojson,hash,compare]

type reference_or_constr =
  [%import: Vernacexpr.reference_or_constr]
  [@@deriving sexp,yojson,hash,compare]

type hints_expr =
  [%import: Vernacexpr.hints_expr]
  [@@deriving sexp,yojson,hash,compare]

type vernac_one_argument_status =
  [%import: Vernacexpr.vernac_one_argument_status]
  [@@deriving sexp,yojson,hash,compare]

type vernac_argument_status =
  [%import: Vernacexpr.vernac_argument_status]
  [@@deriving sexp,yojson,hash,compare]

type arguments_modifier =
  [%import: Vernacexpr.arguments_modifier]
  [@@deriving sexp,yojson,hash,compare]

type option_setting =
  [%import: Vernacexpr.option_setting]
  [@@deriving sexp,yojson,hash,compare]

type notation_enable_modifier =
  [%import: Vernacexpr.notation_enable_modifier]
  [@@deriving sexp, yojson,hash,compare]

type vernac_expr =
  [%import: Vernacexpr.vernac_expr]
  [@@deriving sexp,yojson,hash,compare]

type control_flag =
  [%import: Vernacexpr.control_flag]
  [@@deriving sexp,yojson,hash,compare]

type vernac_control_r =
  [%import: Vernacexpr.vernac_control_r]
  [@@deriving sexp,yojson,hash,compare]

type vernac_control =
  [%import: Vernacexpr.vernac_control]
  [@@deriving sexp,yojson,hash,compare]
