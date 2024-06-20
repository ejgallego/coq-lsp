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

module Loc = Ser_loc

module Xml_datatype = Ser_xml_datatype
module Pp           = Ser_pp
module Stateid      = Ser_stateid

type level =
  [%import: Feedback.level]
  [@@deriving sexp, yojson]

type route_id =
  [%import: Feedback.route_id]
  [@@deriving sexp, yojson]

type doc_id =
  [%import: Feedback.doc_id]
  [@@deriving sexp, yojson]

type feedback_content =
  [%import: Feedback.feedback_content]
  [@@deriving sexp, yojson]

type feedback =
  [%import: Feedback.feedback]
  [@@deriving sexp, yojson]

