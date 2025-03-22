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
module Declarations = Ser_declarations
module Mod_subst = Ser_mod_subst
module Retroknowledge = Ser_retroknowledge

module MBO =
struct
type t = Mod_declarations.module_body
let name = "module_body"
end

module MTO =
struct
type t = Mod_declarations.module_type_body
let name = "module_type_body"
end

module MB = SerType.Opaque(MBO)
module MT = SerType.Opaque(MTO)

type module_body = MB.t
  [@@deriving sexp,yojson,hash,compare]

type module_type_body = MT.t
  [@@deriving sexp,yojson,hash,compare]

type structure_body =
  [%import: Mod_declarations.structure_body]
  [@@deriving sexp,yojson,hash,compare]

type module_signature =
  [%import: Mod_declarations.module_signature]
  [@@deriving sexp,yojson,hash,compare]
