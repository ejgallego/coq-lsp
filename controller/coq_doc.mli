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

module G = Serapi.Serapi_goals

(* [node list] is a very crude form of a meta-data map "loc -> data" , where for
   now [data] is only the goals. *)
type node =
  { ast : Coq_ast.t  (** Ast of node *)
  ; state : Coq_state.t  (** (Full) State of node *)
  ; goal : Pp.t G.reified_goal G.ser_goals option
        (** Goal of node / to be made lazy *)
  ; feedback : Pp.t Loc.located list  (** Messages relative to the node *)
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
  -> fb_queue:Pp.t Loc.located list ref
  -> t * Coq_state.t * Lsp.Base.Diagnostic.t list
