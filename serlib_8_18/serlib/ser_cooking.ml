(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016-2019 MINES ParisTech                                  *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

module Names = Ser_names
module Univ = Ser_univ
module Constr = Ser_constr

type abstr_info = {
  abstr_ctx : Constr.named_context;
  abstr_auctx : Univ.AbstractContext.t;
  abstr_ausubst : Univ.Instance.t;
} [@@deriving sexp,yojson,hash,compare]

type abstr_inst_info = {
  abstr_rev_inst : Names.Id.t list;
  abstr_uinst : Univ.Instance.t;
} [@@deriving sexp,yojson,hash,compare]

type 'a entry_map = 'a Names.Cmap.t * 'a Names.Mindmap.t [@@deriving sexp,yojson,hash,compare]
type expand_info = abstr_inst_info entry_map [@@deriving sexp,yojson,hash,compare]

module CIP = struct
type _t = {
  expand_info : expand_info;
  abstr_info : abstr_info;
} [@@deriving sexp,yojson,hash,compare]

type t =
  [%import: Cooking.cooking_info]
end

module B_ = SerType.Pierce(CIP)
type cooking_info = B_.t
 [@@deriving sexp,yojson,hash,compare]
