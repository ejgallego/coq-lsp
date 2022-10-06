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

(* [node list] is a very crude form of a meta-data map "loc -> data" , where for
   now [data] is only the goals. *)
type node =
  { ast : Coq.Ast.t  (** Ast of node *)
  ; state : Coq.State.t  (** (Full) State of node *)
  ; memo_info : string
  }

type t =
  { uri : string
  ; version : int
  ; contents : string
  ; root : Coq.State.t
  ; nodes : node list
  }

val create :
     state:Coq.State.t * Loadpath.vo_path list * string list * _
  -> uri:string
  -> version:int
  -> contents:string
  -> t

val check :
     ofmt:Format.formatter
  -> doc:t
  -> fb_queue:Coq.Message.t list ref
  -> t * Coq.State.t * Types.Diagnostic.t list
