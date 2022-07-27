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

type node =
  { ast : Coq_ast.t
  ; goal : Pp.t option
  }

type t =
  { uri : string
  ; version : int
  ; contents : string
  ; root : Coq_state.t
  ; nodes : node list
  }

val create :
     state:Coq_state.t * Loadpath.vo_path list * string list * _
  -> uri:string
  -> version:int
  -> contents:string
  -> t

val check :
     ofmt:Format.formatter
  -> doc:t
  -> fb_queue:Pp.t list ref
  -> t * Coq_state.t * Yojson.Basic.t
