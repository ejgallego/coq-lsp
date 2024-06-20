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

module Names = Ser_names

module OD = struct
  type t = Mod_subst.delta_resolver
  let name = "Mod_subst.delta_resolver"
end

module A_ = SerType.Opaque(OD)
type delta_resolver = A_.t
 [@@deriving sexp,yojson,hash,compare]

module OS = struct
  type t = Mod_subst.substitution
  let name = "Mod_subst.substitution"
end

module B_ = SerType.Opaque(OS)
type substitution = B_.t
 [@@deriving sexp,yojson,hash,compare]
