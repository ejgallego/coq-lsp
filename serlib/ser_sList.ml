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

module SL = struct

  type 'a _t =
    | Nil
    | Cons of 'a * 'a _t
    | Default of int * 'a _t
  [@@deriving sexp,yojson,hash,compare]

  type 'a t = 'a SList.t

end

include SerType.Pierce1(SL)

let rec _map f = function
  | SL.Nil -> SL.Nil
  | SL.Cons (x, xs) -> SL.Cons (f x, _map f xs)
  | SL.Default (n, l) -> SL.Default (n, _map f l)

let map (f : 'a -> 'b) (x : 'a SList.t) : 'b SList.t = Obj.magic (_map f (Obj.magic x))
