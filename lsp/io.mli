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

(** Read a JSON-RPC request from channel *)
val read_raw_request : in_channel -> Yojson.Safe.t

(** *)
val read_request : in_channel -> Base.Message.t

exception ReadError of string

(** Send a JSON-RPC request to channel *)
val send_json : Format.formatter -> Yojson.Safe.t -> unit

(** Logging *)

(** Trace values *)
module TraceValue : sig
  type t =
    | Off
    | Messages
    | Verbose

  val of_string : string -> t
  val to_string : t -> string
end

(** Set the trace value *)
val set_trace_value : TraceValue.t -> unit

(** Set the log channel *)
val set_log_channel : Format.formatter -> unit

(** Send a [window/logMessage] notification to the client *)
val logMessage : lvl:int -> message:string -> unit

(** Send a [$/logTrace] notification to the client *)
val logTrace : message:string -> extra:string option -> unit

(** [log hdr ?extra message] Log [message] to server info log with header [hdr].
    [extra] will be used when [trace_value] is set to [Verbose] *)
val trace : string -> ?extra:string -> string -> unit

(** Log JSON object to server info log *)
val trace_object : string -> Yojson.Safe.t -> unit
