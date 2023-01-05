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
  { loc : Loc.t
  ; ast : Coq.Ast.t option  (** Ast of node *)
  ; state : Coq.State.t  (** (Full) State of node *)
  ; diags : Types.Diagnostic.t list  (** Diagnostics associated to the node *)
  ; messages : Coq.Message.t list
  ; memo_info : string
  }

module Completion : sig
  type t =
    | Yes of Loc.t  (** Location of the last token in the document *)
    | Stopped of Loc.t  (** Location of the last valid token *)
end

type t = private
  { uri : string
  ; version : int
  ; contents : string
  ; end_loc : int * int * int
  ; root : Coq.State.t
  ; nodes : node list
  ; diags_dirty : bool
  ; completed : Completion.t
  }

val create :
     state:Coq.State.t
  -> workspace:Coq.Workspace.t
  -> uri:string
  -> version:int
  -> contents:string
  -> t

val bump_version : version:int -> contents:string -> t -> t

val check :
  ofmt:Format.formatter -> doc:t -> fb_queue:Coq.Message.t list ref -> t
