(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

exception Ser_error of string

let _ = CErrors.register_handler (function
    | Ser_error msg ->
      Some Pp.(seq [str "Serlib Error: "; str msg])
    | _ ->
      None)

let opaque_of_sexp ~typ _obj =
  raise (Ser_error ("["^typ^": ABSTRACT / cannot deserialize]"))

let exn_on_opaque = ref true

let sexp_of_opaque ~typ _exp =
  let msg = "["^typ^": ABSTRACT]" in
  if !exn_on_opaque then
    raise (Ser_error msg)
  else
    Sexplib.Sexp.Atom ("["^typ^": ABSTRACT]")

let opaque_of_yojson ~typ _obj =
  raise (Ser_error ("["^typ^": ABSTRACT / cannot deserialize]"))

let opaque_to_yojson ~typ _obj =
  let msg = "["^typ^": ABSTRACT]" in
  if !exn_on_opaque then
    raise (Ser_error msg)
  else
    `String ("["^typ^": ABSTRACT]")

let hash_opaque ~typ:_ x = Hashtbl.hash x
let hash_fold_opaque ~typ st x = Ppx_hash_lib.Std.Hash.Builtin.hash_fold_int st (hash_opaque ~typ x)
let compare_opaque ~typ:_ x y = Stdlib.compare x y

