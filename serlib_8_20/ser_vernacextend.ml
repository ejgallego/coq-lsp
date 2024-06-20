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

module Names = Ser_names

(* type vernac_type =
 *   [%import: Vernacextend.vernac_type]
 *   [@@deriving sexp] *)
type vernac_keep_as =
  [%import: Vernacextend.vernac_keep_as]
  [@@deriving sexp]
and vernac_qed_type =
  [%import: Vernacextend.vernac_qed_type]
  [@@deriving sexp]
and vernac_when =
  [%import: Vernacextend.vernac_when]
  [@@deriving sexp]
and vernac_start =
  [%import: Vernacextend.vernac_start]
  [@@deriving sexp]
and vernac_sideff_type =
  [%import: Vernacextend.vernac_sideff_type]
  [@@deriving sexp]
and opacity_guarantee =
  [%import: Vernacextend.opacity_guarantee]
  [@@deriving sexp]
and solving_tac =
  [%import: Vernacextend.solving_tac]
  [@@deriving sexp]
and anon_abstracting_tac =
  [%import: Vernacextend.anon_abstracting_tac]
  [@@deriving sexp]
and proof_block_name =
  [%import: Vernacextend.proof_block_name]
  [@@deriving sexp]
