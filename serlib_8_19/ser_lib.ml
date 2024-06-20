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

module Nametab = Ser_nametab
module Libobject = Ser_libobject
module Summary = Ser_summary

type is_type =
  [%import: Lib.is_type]
  [@@deriving sexp]

type export_flag =
  [%import: Lib.export_flag]
  [@@deriving sexp]

type export =
  [%import: Lib.export]
  [@@deriving sexp]

type 'a node =
  [%import: 'a Lib.node]
  [@@deriving sexp]

type 'a library_segment =
  [%import: 'a Lib.library_segment]
  [@@deriving sexp]
