(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: LSP Controller Core                    *)
(*************************************************************************)

module Lsp = Fleche_lsp

(** This is the platform-independent code for the implementation of the Flèche
    LSP interface, BEWARE of deps, this must be able to run in a Web Worker
    context *)

module State : sig
  type t =
    { cmdline : Coq.Workspace.CmdLine.t
    ; root_state : Coq.State.t
    ; workspaces : (string * (Coq.Workspace.t, string) Result.t) list
    ; default_workspace : Coq.Workspace.t  (** fail safe *)
    }
end

exception Lsp_exit

(** Lsp special init loop *)
module Init_effect : sig
  type t =
    | Success of (string * (Coq.Workspace.t, string) Result.t) list
    (* List of workspace roots, + maybe an associated Coq workspace for the
       path *)
    | Loop
    | Exit
end

val lsp_init_process :
     ofn:(Lsp.Base.Message.t -> unit)
  -> io:Fleche.Io.CallBack.t
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
     io:Fleche.Io.CallBack.t
  -> ofn:(Lsp.Base.Message.t -> unit)
  -> state:State.t
  -> State.t cont option

(** Add a message to the queue *)
val enqueue_message : Lsp.Base.Message.t -> unit

(** Generic output handler *)
module CB (O : sig
  val ofn : Lsp.Base.Notification.t -> unit
end) : sig
  val cb : Fleche.Io.CallBack.t
end
