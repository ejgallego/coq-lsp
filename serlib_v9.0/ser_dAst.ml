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

let thunk_of_yojson : type a b. (Yojson.Safe.t -> (a, string) Result.t) -> (Yojson.Safe.t -> (b, string) Result.t) -> Yojson.Safe.t -> ((a,b) thunk, string) Result.t =
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
