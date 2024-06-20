(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+ *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module type ExtS = sig

  include CSig.MapS

  (* module SSet : Ser_cSet.ExtS *)

  include SerType.SJHC1 with type 'a t := 'a t

end

module Make (M : CSig.MapS) (S : SerType.SJHC with type t = M.key) = struct

  include M

  module BijectSpec = struct

    type 'a t = 'a M.t
    type 'a _t = (S.t * 'a) list
    [@@deriving sexp,yojson,hash,compare]

    let to_t l = List.fold_left (fun e (k,s) -> M.add k s e) M.empty l
    let of_t = M.bindings
  end

  include SerType.Biject1(BijectSpec)

end
