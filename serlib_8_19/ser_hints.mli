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

type hint_db_name = Hints.hint_db_name
 [@@deriving sexp,yojson,hash,compare]

type 'a hints_path_gen = 'a Hints.hints_path_gen
 [@@deriving sexp,yojson,hash,compare]

type 'a hints_path_atom_gen = 'a Hints.hints_path_atom_gen
 [@@deriving sexp,yojson,hash,compare]

type hints_path = Hints.hints_path
 [@@deriving sexp,yojson,hash,compare]

type 'a hints_transparency_target = 'a Hints.hints_transparency_target [@@deriving sexp,yojson,hash,compare]
type hint_mode = Hints.hint_mode [@@deriving sexp,yojson,hash,compare]
