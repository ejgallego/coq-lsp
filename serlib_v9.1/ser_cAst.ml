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

module Loc        = Ser_loc

module L = struct
type 'a t = {
  v   : 'a;
  loc : Loc.t option [@ignore] [@hash.ignore];
} [@@deriving sexp,yojson,hash,compare]
end

type 'a t = 'a CAst.t = private {
  v   : 'a;
  loc : Loc.t option;
}

let t_of_sexp f s = let { L.v ; loc } = L.t_of_sexp f s in CAst.make ?loc:loc v
let sexp_of_t f { CAst.v ; loc } = L.sexp_of_t f { L.v ; loc }

let of_yojson f json = Ppx_deriving_yojson_runtime.(L.of_yojson f json >|= fun { L.v; loc } -> CAst.make ?loc:loc v)
let to_yojson f { CAst.v ; loc } = L.to_yojson f { L.v ; loc }

let hash_fold_t f st { CAst.v; loc } = L.hash_fold_t f st { L.v; loc }

let compare f { CAst.v = v1; loc = l1 } { CAst.v = v2; loc = l2 } = L.compare f { L.v = v1; loc = l1 } { L.v = v2; loc = l2 }

let omit_att = ref false

let sexp_of_t f x =
  if !omit_att then f x.CAst.v else sexp_of_t f x

(* let to_yojson f x =
   if !omit_att then ... *)

