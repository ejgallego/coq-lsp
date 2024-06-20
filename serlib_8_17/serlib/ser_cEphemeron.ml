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

module EBiject = struct
  type 'a t = 'a CEphemeron.key

  type 'a _t = 'a [@@deriving sexp,yojson,hash,compare]

  let to_t x = CEphemeron.create x
  let of_t x = CEphemeron.get x
end

module B = SerType.Biject1(EBiject)
type 'a key = 'a B.t
 [@@deriving sexp,yojson,hash,compare]
