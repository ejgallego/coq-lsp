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

  include CSig.UMapS

  (* module SSet : Ser_cSet.ExtS *)

  include SerType.SJHC1 with type 'a t := 'a t

end

module Make (M : CSig.UMapS) (S : SerType.SJHC with type t = M.key) = struct

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
