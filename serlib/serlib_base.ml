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

