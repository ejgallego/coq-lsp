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
