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
(* Coq Language Server Protocol                                         *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

type ast = Vernacexpr.vernac_expr CAst.t

type node =
  { ast  : ast
  ; exec : bool
  }

type t =
  { uri : string
  ; version: int
  ; contents : string
  ; root : Vernacstate.t
  ; nodes : node list
  }

val create
  :  uri:string
  -> version:int
  -> contents:string
  -> t

val check
  :  doc:t
  -> Vernacstate.t * Yojson.Basic.t
