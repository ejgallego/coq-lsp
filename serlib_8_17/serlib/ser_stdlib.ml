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

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

type nonrec 'a ref = 'a Stdlib.ref

let ref x = ref x
let (!) x = !x
let (:=) x v = x := v
let ref_of_sexp = ref_of_sexp
let sexp_of_ref = sexp_of_ref
let ref_to_yojson f x = f !x
let ref_of_yojson f x = Result.map (fun x -> ref x) (f x)
let hash_fold_ref = hash_fold_ref_frozen
let compare_ref = compare_ref

let (==) = Stdlib.(==)

module Lazy = struct
  type 'a t = 'a lazy_t
  [@@deriving sexp]
end

module List = struct
  type 'a t = 'a list
  [@@deriving sexp]
end

module Option = Stdlib.Option
