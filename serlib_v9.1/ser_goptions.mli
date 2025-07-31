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

type option_locality = Goptions.option_locality
[@@deriving sexp, yojson, hash,compare]

type option_name = Goptions.option_name
[@@deriving sexp, yojson, hash,compare]

type option_value = Goptions.option_value
 [@@deriving sexp,yojson,hash,compare]

type option_state = Goptions.option_state
 [@@deriving sexp,yojson,hash,compare]

type table_value = Goptions.table_value [@@deriving sexp, yojson, hash,compare]
