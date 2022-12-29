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

(* We export this module *)
module TraceValue : sig
  type t =
    | Off
    | Messages
    | Verbose

  val parse : string -> t
  val to_string : t -> string
end

val set_trace_value : TraceValue.t -> unit

(** Read a JSON-RPC request from channel *)
val read_request : in_channel -> Yojson.Safe.t

exception ReadError of string

(** Send a JSON-RPC request to channel *)
val send_json : Format.formatter -> Yojson.Safe.t -> unit

(** Send a [window/logMessage] notification to the client *)
val logMessage : Format.formatter -> lvl:int -> message:string -> unit

(** Send a [$/logTrace] notification to the client *)
val logTrace : Format.formatter -> verbose:string -> message:string -> unit

(** Log string to server info log *)
val log_info : string -> string -> unit

(** Log string to server error log *)
val log_error : string -> string -> unit

(** Log JSON object to server info log *)
val log_object : string -> Yojson.Safe.t -> unit
