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

module Loc           = Ser_loc
module Notation_term = Ser_notation_term
module Notation_gram = Ser_notation_gram
module Constrexpr    = Ser_constrexpr
module Extend        = Ser_extend

type ppbox =
  [%import: Ppextend.ppbox]
  [@@deriving sexp, yojson]

type ppcut =
  [%import: Ppextend.ppcut]
  [@@deriving sexp, yojson]

type pattern_quote_style =
  [%import: Ppextend.pattern_quote_style]
  [@@deriving sexp, yojson]

type unparsing =
  [%import: Ppextend.unparsing]
  [@@deriving sexp]

type unparsing_rule =
  [%import: Ppextend.unparsing_rule]
  [@@deriving sexp]

type notation_printing_rules =
  [%import: Ppextend.notation_printing_rules]
  [@@deriving sexp]
