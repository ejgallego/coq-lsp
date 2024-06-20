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

module Names = Ser_names

module RawLevel = struct

  module UGlobal = struct
    type t = Names.DirPath.t * int
    [@@deriving sexp, yojson, hash,compare]
  end

  type t =
  | SProp
  | Prop
  | Set
  | Level of UGlobal.t
  | Var of int
  [@@deriving sexp, yojson, hash,compare]

end

module Level = struct
  module PierceSpec = struct
    type t = Univ.Level.t
    type _t =
      { hash : int
      ; data : RawLevel.t
      } [@@deriving sexp, yojson, hash,compare]
  end

  module PierceImp = SerType.Pierce(PierceSpec)
  include PierceImp
  module Set = Ser_cSet.Make(Univ.Level.Set)(PierceImp)
end

(* XXX: Think what to do with this  *)
module Universe = struct

  module PierceSpec = struct

    type t = Univ.Universe.t
    type _t = (Level.t * int) list
    [@@deriving sexp,yojson,hash,compare]
  end

  include SerType.Pierce(PierceSpec)
end

(*************************************************************************)

type constraint_type =
  [%import: Univ.constraint_type]
  [@@deriving sexp,yojson,hash,compare]

type univ_constraint =
  [%import: Univ.univ_constraint]
  [@@deriving sexp,yojson,hash,compare]

module Constraints = Ser_cSet.Make(Univ.Constraints)(struct
    type t = univ_constraint
    let t_of_sexp = univ_constraint_of_sexp
    let sexp_of_t = sexp_of_univ_constraint
    let of_yojson = univ_constraint_of_yojson
    let to_yojson = univ_constraint_to_yojson
    let hash = hash_univ_constraint
    let hash_fold_t = hash_fold_univ_constraint
    let compare = compare_univ_constraint
  end)

type 'a constrained =
  [%import: 'a Univ.constrained]
  [@@deriving sexp,yojson,hash,compare]

module ContextSet = struct
  type t =
    [%import: Univ.ContextSet.t]
    [@@deriving sexp, yojson, hash, compare]
end

type 'a in_universe_context_set =
  [%import: 'a Univ.in_universe_context_set]
  [@@deriving sexp]
