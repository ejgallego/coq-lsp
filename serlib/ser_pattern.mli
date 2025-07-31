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

type patvar = Pattern.patvar [@@deriving sexp,yojson,hash,compare]

type case_info_pattern = Pattern.case_info_pattern
  [@@deriving sexp,yojson,hash,compare]

type 'i uninstantiated_pattern = 'i Pattern.uninstantiated_pattern
  [@@deriving sexp,yojson,hash,compare]

type constr_pattern = Pattern.constr_pattern
  [@@deriving sexp,yojson,hash,compare]
