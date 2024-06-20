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
