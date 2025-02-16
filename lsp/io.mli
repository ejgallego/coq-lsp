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

(** {1} JSON-RPC input/output *)

(** Read a JSON-RPC message from channel; [None] signals [EOF] *)
val read_message : in_channel -> (Base.Message.t, string) Result.t option

(** Send a JSON-RPC message to channel *)
val send_message : Format.formatter -> Base.Message.t -> unit

(** {1} Imperative Logging and Tracing using [log_fn] *)

(** Set the log output function *)
val set_log_fn : (Base.Notification.t -> unit) -> unit

(** Send a [window/logMessage] notification to the client using [log_fn] *)
val logMessageInt : lvl:int -> message:string -> unit

module Lvl : sig
  type t = Fleche.Io.Level.t =
    | Error
    | Warning
    | Info
    | Log
    | Debug

  val to_int : t -> int
end

(** Send a [window/logMessage] notification to the client using [log_fn] *)
val logMessage : lvl:Lvl.t -> message:string -> unit

(** Trace values *)
module TraceValue : sig
  type t =
    | Off
    | Messages
    | Verbose

  val of_string : string -> (t, string) Result.t
  val to_string : t -> string
end

(** Set the trace value *)
val set_trace_value : TraceValue.t -> unit

(** Send a [$/logTrace] notification to the client *)
val logTrace : message:string -> extra:string option -> unit
