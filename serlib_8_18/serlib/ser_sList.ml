(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2022 Inria                                                 *)
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
