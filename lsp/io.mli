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

(** JSON-RPC input/output *)

(** Set the log function *)
val set_log_fn : (Base.Notification.t -> unit) -> unit

(** Read a JSON-RPC message from channel; [None] signals [EOF] *)
val read_message : in_channel -> (Base.Message.t, string) Result.t option

(** Send a JSON-RPC message to channel *)
val send_message : Format.formatter -> Base.Message.t -> unit

(** Logging *)

(** Trace values *)
module TraceValue : sig
  type t =
    | Off
    | Messages
    | Verbose

  val of_string : string -> (t, string) result
  val to_string : t -> string
end

(** Set the trace value *)
val set_trace_value : TraceValue.t -> unit

module Lvl : sig
  (* 1-5 *)
  type t =
    | Error
    | Warning
    | Info
    | Log
    | Debug
end

module MessageParams : sig
  val method_ : string

  type t =
    { type_ : int [@key "type"]
    ; message : string
    }
  [@@deriving yojson]
end

(** Create a logMessage notification *)
val mk_logMessage : type_:int -> message:string -> Base.Notification.t

(** Send a [window/logMessage] notification to the client *)
val logMessage : lvl:Lvl.t -> message:string -> unit

(** Send a [window/logMessage] notification to the client *)
val logMessageInt : lvl:int -> message:string -> unit

module TraceParams : sig
  val method_ : string

  type t =
    { message : string
    ; verbose : string option [@default None]
    }
  [@@deriving yojson]
end

(** Create a logTrace notification *)
val mk_logTrace : message:string -> extra:string option -> Base.Notification.t

(** Send a [$/logTrace] notification to the client *)
val logTrace : message:string -> extra:string option -> unit

(** [log hdr ?extra message] Log [message] to server info log with header [hdr].
    [extra] will be used when [trace_value] is set to [Verbose] *)
val trace : string -> ?extra:string -> string -> unit

(** Log JSON object to server info log *)
val trace_object : string -> Yojson.Safe.t -> unit
