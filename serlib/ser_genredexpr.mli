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

type 'a red_atom = 'a Genredexpr.red_atom
 [@@deriving sexp,yojson,hash,compare]

type 'a glob_red_flag =  'a Genredexpr.glob_red_flag
 [@@deriving sexp,yojson,hash,compare]

type ('a, 'b, 'c, 'd) red_expr_gen =  ('a, 'b, 'c, 'd) Genredexpr.red_expr_gen
  [@@deriving sexp,yojson,hash,compare]

type ('a, 'b, 'c, 'd) may_eval =  ('a, 'b, 'c, 'd) Genredexpr.may_eval
  [@@deriving sexp,yojson,hash,compare]

type raw_red_expr = Genredexpr.raw_red_expr [@@deriving sexp,yojson,hash,compare]

type 'a and_short_name = 'a Genredexpr.and_short_name
  [@@deriving sexp,yojson,hash,compare]

type glob_red_expr = Genredexpr.glob_red_expr
  [@@deriving sexp,yojson,hash,compare]
