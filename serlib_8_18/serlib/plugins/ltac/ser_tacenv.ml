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
(* Copyright 2016-2018 MINES ParisTech                                  *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

open Sexplib.Std
open Serlib

module Names        = Ser_names
module Deprecation  = Ser_deprecation

module Ltac_plugin = struct
  module Tacexpr = Ser_tacexpr
  module Tacenv  = Ltac_plugin.Tacenv
end

open Ltac_plugin [@@ocaml.warning "-33"]

type ltac_entry =
  [%import: Ltac_plugin.Tacenv.ltac_entry]
  [@@deriving sexp]

