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

open Sexplib.Conv

module Stateid      = Ser_stateid
module Future       = Ser_future
module Names        = Ser_names
module Univ         = Ser_univ
module UVars        = Ser_uvars
module Constr       = Ser_constr
module Declarations = Ser_declarations
module CPrimitives  = Ser_cPrimitives

(* type local_entry =
 *   [%import: Entries.local_entry]
 *   [@@deriving sexp] *)

(* type inductive_universes =
 *   [%import: Entries.inductive_universes]
 *   [@@deriving sexp] *)

type universes_entry =
  [%import: Entries.universes_entry]
  [@@deriving sexp]

type 'a in_universes_entry =
  [%import: 'a Entries.in_universes_entry]
  [@@deriving sexp]

type one_inductive_entry =
  [%import: Entries.one_inductive_entry]
  [@@deriving sexp]

type variance_entry =
  [%import: Entries.variance_entry]
  [@@deriving sexp]

(* type mutual_inductive_entry =
 *   [%import: Entries.mutual_inductive_entry]
 *   [@@deriving sexp] *)

type 'a proof_output =
  [%import: 'a Entries.proof_output]
  [@@deriving sexp]

(* type 'a const_entry_body =
 *   [%import: 'a Entries.const_entry_body]
 *   [@@deriving sexp] *)

(* type constant_universes_entry =
 *   [%import: Entries.constant_universes_entry]
 *   [@@deriving sexp] *)

(* type 'a in_constant_universes_entry =
 *   [%import: 'a Entries.in_constant_universes_entry]
 *   [@@deriving sexp] *)

type definition_entry =
  [%import: Entries.definition_entry]
  [@@deriving sexp]

type section_def_entry =
  [%import: Entries.section_def_entry]
  [@@deriving sexp]

type inline =
  [%import: Entries.inline]
  [@@deriving sexp]

type 'a opaque_entry =
  [%import: 'a Entries.opaque_entry]
  [@@deriving sexp]

type parameter_entry =
  [%import: Entries.parameter_entry]
  [@@deriving sexp]

type primitive_entry =
  [%import: Entries.primitive_entry]
  [@@deriving sexp]

type constant_entry =
  [%import: Entries.constant_entry]
  [@@deriving sexp]

type module_struct_entry =
  [%import: Entries.module_struct_entry]
  [@@deriving sexp]

type module_params_entry =
  [%import: Entries.module_params_entry]
  [@@deriving sexp]

type module_entry =
  [%import: Entries.module_entry]
  [@@deriving sexp]

type module_type_entry =
  [%import: Entries.module_type_entry]
  [@@deriving sexp]

(* type seff_env =
 *   [%import: Entries.seff_env]
 *   [@@deriving sexp] *)

(* type side_effect_role =
 *   [%import: Entries.side_effect_role]
 *   [@@deriving sexp] *)

(* type side_eff =
 *   [%import: Entries.side_eff]
 *   [@@deriving sexp] *)
