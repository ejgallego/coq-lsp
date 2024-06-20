(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(* We force the thunks in serialization *)

open Sexplib

module CAst = Ser_cAst

type ('a, 'b) thunk =
  [%import: ('a,'b) DAst.thunk]

let sexp_of_thunk : type a b. (a -> Sexp.t) -> (b -> Sexp.t) -> (a,b) thunk -> Sexp.t =
  fun f _ t -> match t with
  | Value v -> f v
  | Thunk t -> f (Lazy.force t)

let thunk_of_sexp : type a b. (Sexp.t -> a) -> (Sexp.t -> b) -> Sexp.t -> (a,b) thunk =
  fun f _ s -> Value (f s)

let thunk_of_yojson : type a b. (Yojson.Safe.t -> (a, string) Result.result) -> (Yojson.Safe.t -> (b, string) Result.result) -> Yojson.Safe.t -> ((a,b) thunk, string) Result.result =
  fun f _ s -> Result.map (fun s -> Value s) (f s)

let thunk_to_yojson : type a b. (a -> Yojson.Safe.t) -> (b -> Yojson.Safe.t) -> (a,b) thunk -> Yojson.Safe.t =
  fun f _ t -> match t with
  | Value v -> f v
  | Thunk t -> f (Lazy.force t)

let _hash : type a b. (a -> int) -> (b -> int) -> (a,b) thunk -> int =
  fun f _ t -> match t with
  | Value v -> f v
  | Thunk t -> f (Lazy.force t)

let hash_fold_thunk : type a b. (a Ppx_hash_lib.Std.Hash.folder) -> (b Ppx_hash_lib.Std.Hash.folder) -> (a,b) thunk Ppx_hash_lib.Std.Hash.folder =
    fun f _ st t -> match t with
  | Value v -> f st v
  | Thunk t -> f st (Lazy.force t)

let compare_thunk : type a b. (a Ppx_compare_lib.compare) -> (b Ppx_compare_lib.compare) -> (a,b) thunk Ppx_compare_lib.compare =
  fun f _ t1 t2 -> match t1,t2 with
  | Value v1, Value v2 -> f v1 v2
  | Thunk t1, Value v2 -> f (Lazy.force t1) v2
  | Value v1, Thunk t2 -> f v1 (Lazy.force t2)
  | Thunk t1, Thunk t2 -> f (Lazy.force t1) (Lazy.force t2)

type ('a, 'b) t =
  [%import: ('a, 'b) DAst.t]
  [@@deriving sexp,yojson,hash,compare]
