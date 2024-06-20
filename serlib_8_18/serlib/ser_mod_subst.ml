(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

(* open Sexplib.Std *)

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
