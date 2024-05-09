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

module Vmemitcodes = Ser_vmemitcodes

module OP = struct
type t = Vmlibrary.t
let name = "Vmlibrary.t"
end

module B = SerType.Opaque(OP)
type t = B.t
 [@@deriving sexp,yojson,hash,compare]

module OQ = struct
type t = Vmlibrary.index
let name = "Vmlibrary.index"
end

module C = SerType.Opaque(OQ)
type index = C.t
 [@@deriving sexp,yojson,hash,compare]

type indirect_code = index Vmemitcodes.pbody_code [@@deriving sexp,yojson,hash,compare]
