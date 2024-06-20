(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2017 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(* open Sexplib *)
(* open Sexplib.Std *)

module Constr  = Ser_constr
module Environ = Ser_environ

module ECtoC = struct

  type t = EConstr.t
  type _t = Constr.t
  [@@deriving sexp,yojson,hash,compare]

  let to_t = EConstr.of_constr
  let of_t = EConstr.Unsafe.to_constr
end

include SerType.Biject(ECtoC)

type existential =
  [%import: EConstr.existential]
  [@@deriving sexp]

type constr =
  [%import: EConstr.constr]
  [@@deriving sexp,yojson,hash,compare]

type types =
  [%import: EConstr.types]
  [@@deriving sexp]

type unsafe_judgment =
  [%import: EConstr.unsafe_judgment]
  [@@deriving sexp]

