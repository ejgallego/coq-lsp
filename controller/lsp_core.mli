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
    { cmdline : Coq.Workspace.CmdLine.t
    ; root_state : Coq.State.t
    ; workspaces : (string * Coq.Workspace.t) list
    }
end

exception Lsp_exit

(** Lsp special init loop *)
module Init_effect : sig
  type t =
    | Success of (string * Coq.Workspace.t) list
    | Loop
    | Exit
end

val lsp_init_process :
     ofn:(Yojson.Safe.t -> unit)
  -> cmdline:Coq.Workspace.CmdLine.t
  -> debug:bool
  -> Lsp.Base.Message.t
  -> Init_effect.t

(** Actions the scheduler requests to callers *)
type 'a cont =
  | Cont of 'a
  | Yield of 'a

(** Core scheduler: dispatch an LSP request or notification, check document and
    wake up pending requests *)
val dispatch_or_resume_check :
  ofn:(Yojson.Safe.t -> unit) -> state:State.t -> State.t cont option

(** Add a message to the queue *)
val enqueue_message : Lsp.Base.Message.t -> unit
