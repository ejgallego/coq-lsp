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

module NumTok     = Ser_numTok

type t =
  [%import: Tok.t]
  [@@deriving sexp]

type 'c p =
  [%import: 'c Tok.p]
  [@@deriving sexp_of]

(** GADTS...  *)
type 'c _p =
  | PKEYWORD of string
  | PPATTERNIDENT of string option
  | PIDENT of string option
  | PFIELD of string option
  | PNUMERAL of NumTok.Unsigned.t option
  | PSTRING of string option
  | PLEFTQMARK
  | PBULLET of string option
  | PQUOTATION of string
  | PEOI
  [@@deriving of_sexp]

let p_of_sexp f x = Obj.magic (_p_of_sexp f x)
