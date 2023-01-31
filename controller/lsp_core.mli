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
(* Copyright 2019-2022 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(** This is the platform-independent code for the implementation of the Flèche
    LSP interface, BEWARE of deps, this must be able to run in a Web Worker
    context *)

module State : sig
  type t =
    { root_state : Coq.State.t
    ; workspace : Coq.Workspace.t
    }
end

exception Lsp_exit

(** Lsp special init loop *)
val lsp_init_loop :
     in_channel
  -> Format.formatter
  -> cmdline:Coq.Workspace.CmdLine.t
  -> debug:bool
  -> Coq.Workspace.t

(** Dispatch an LSP request or notification, requests may be postponed. *)
val dispatch_message :
  ofmt:Format.formatter -> state:State.t -> Lsp.Base.Message.t -> unit

(** Serve postponed requests in the set, they can be stale *)
val serve_postponed_requests : ofmt:Format.formatter -> Int.Set.t -> unit
