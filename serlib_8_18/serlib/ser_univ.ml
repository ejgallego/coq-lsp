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

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

let hash_fold_array = hash_fold_array_frozen

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

module Variance = struct

  type t =
    [%import: Univ.Variance.t]
  [@@deriving sexp,yojson,hash,compare]

end

module Instance = struct

type t =
  [%import: Univ.Instance.t]

type _t = Instance of Level.t array
  [@@deriving sexp, yojson, hash, compare]

let _instance_put instance            = Instance (Univ.Instance.to_array instance)
let _instance_get (Instance instance) = Univ.Instance.of_array instance

let t_of_sexp sexp     = _instance_get (_t_of_sexp sexp)
let sexp_of_t instance = sexp_of__t (_instance_put instance)

let of_yojson json  =
  Ppx_deriving_yojson_runtime.(_t_of_yojson json >|= _instance_get)
let to_yojson level = _t_to_yojson (_instance_put level)

let hash i = hash__t (Instance (Univ.Instance.to_array i))
let hash_fold_t st i = hash_fold__t st (Instance (Univ.Instance.to_array i))
let compare i1 i2 = compare__t (Instance (Univ.Instance.to_array i1)) (Instance (Univ.Instance.to_array i2))

end

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

module UContext = struct

  module I = struct
    type t = Univ.UContext.t
    type _t = Names.Name.t array * Instance.t constrained
    [@@deriving sexp,yojson,hash,compare]

    let to_t (un, cs) = Univ.UContext.make un cs
    let of_t uc = Univ.UContext.(names uc, (instance uc, constraints uc))
  end

  include SerType.Biject(I)

end

module AbstractContext = struct

  let hash_fold_array = hash_fold_array_frozen
  module ACPierceDef = struct

    type t = Univ.AbstractContext.t
    type _t = Names.Name.t array constrained
    [@@deriving sexp,yojson,hash,compare]
  end

  include SerType.Pierce(ACPierceDef)

end

module ContextSet = struct
  type t =
    [%import: Univ.ContextSet.t]
    [@@deriving sexp, yojson, hash, compare]
end

type 'a in_universe_context =
  [%import: 'a Univ.in_universe_context]
  [@@deriving sexp]

type 'a in_universe_context_set =
  [%import: 'a Univ.in_universe_context_set]
  [@@deriving sexp]

type 'a puniverses =
  [%import: 'a Univ.puniverses]
  [@@deriving sexp, yojson, hash, compare]
