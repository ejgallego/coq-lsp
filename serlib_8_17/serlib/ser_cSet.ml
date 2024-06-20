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

  include CSig.SetS

  include SerType.SJHC with type t := t

end

module Make (M : CSig.SetS) (S : SerType.SJHC with type t = M.elt) = struct

  include M

  module BijectSpec = struct

    type t = M.t
    type _t = S.t list
    [@@deriving sexp,yojson,hash,compare]

    let to_t = List.fold_left (fun e s -> M.add s e) M.empty
    let of_t = M.elements
  end

  include SerType.Biject(BijectSpec)
end
