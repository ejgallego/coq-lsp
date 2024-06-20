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
(* Copyright 2019-2022 Inria                                            *)
(************************************************************************)

open Sexplib.Std

module Names = Ser_names
module Mod_subst = Ser_mod_subst

module CString = struct
  module Pred = struct
    include CString.Pred
    let t_of_sexp _ = CString.Pred.empty
    let sexp_of_t _ = Sexplib.Sexp.Atom "XXX: CString.Pred.t"
  end
end

type _open_filter =
  | Unfiltered
  | Filtered of CString.Pred.t
  [@@deriving sexp]

let _t_put x = Obj.magic x
let _t_get x = Obj.magic x

type open_filter = [%import: Libobject.open_filter]
let open_filter_of_sexp x = _t_put (_open_filter_of_sexp x)
let sexp_of_open_filter x = sexp_of__open_filter (_t_get x)

module Dyn = struct

  type t = Libobject.Dyn.t

  module Reified = struct

    type t =
      (* | Constant of Internal.Constant.t
       * | Inductive of DeclareInd.Internal.inductive_obj *)
      | TaggedAnon of string
    [@@deriving sexp]

    let to_t (x : Libobject.Dyn.t) =
      let Libobject.Dyn.Dyn (tag, _) = x in
      TaggedAnon (Libobject.Dyn.repr tag)
  end

  let t_of_sexp x = Serlib_base.opaque_of_sexp ~typ:"Libobject.Dyn.t" x
  let sexp_of_t x = Reified.sexp_of_t (Reified.to_t x)
end

type obj =
  [%import: Libobject.obj]
  [@@deriving sexp]

type algebraic_objects =
  [%import: Libobject.algebraic_objects]
and t = [%import: Libobject.t]
and substitutive_objects = [%import: Libobject.substitutive_objects]
[@@deriving sexp]
