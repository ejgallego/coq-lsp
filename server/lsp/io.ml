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

module F = Format
module J = Yojson.Safe

let read_request_raw ic =
  let cl = input_line ic in
  let sin = Scanf.Scanning.from_string cl in
  let raw_obj =
    Scanf.bscanf sin "Content-Length: %d\r" (fun size ->
        let buf = Bytes.create size in
        (* Consume the second \r\n or header *)
        let ohdr = input_line ic in
        (* If the second line is a return, then no more headers *)
        let () =
          if ohdr.[0] = '\r' then ()
          else
            (* Fixme (or use ocaml-lsp) Skip the Content-type header *)
            ignore (input_line ic)
        in
        really_input ic buf 0 size;
        Bytes.to_string buf)
  in
  J.from_string raw_obj

exception ReadError of string

let read_request ic =
  try read_request_raw ic with
  (* if the end of input is encountered while some more characters are needed to
     read the current conversion specification, or the lsp server closes *)
  | End_of_file -> raise (ReadError "EOF")
  (* if the input does not match the format. *)
  | Scanf.Scan_failure msg
  (* if a conversion to a number is not possible. *)
  | Failure msg
  (* if the format string is invalid. *)
  | Invalid_argument msg -> raise (ReadError msg)

let mut = Mutex.create ()
let log = ref (fun _ _ -> ())

let send_json fmt obj =
  Mutex.lock mut;
  if Fleche.Debug.send then !log "send" obj;
  let msg = F.asprintf "%a" J.(pretty_print ~std:true) obj in
  let size = String.length msg in
  F.fprintf fmt "Content-Length: %d\r\n\r\n%s%!" size msg;
  Mutex.unlock mut

(** Logging *)

module TraceValue = struct
  type t =
    | Off
    | Messages
    | Verbose

  let of_string = function
    | "messages" -> Messages
    | "verbose" -> Verbose
    | "off" -> Off
    | _ -> raise (Invalid_argument "TraceValue.parse")

  let to_string = function
    | Off -> "off"
    | Messages -> "messages"
    | Verbose -> "verbose"
end

let oc = ref F.std_formatter
let set_log_channel c = oc := c
let trace_value = ref TraceValue.Off
let set_trace_value value = trace_value := value

let logMessage ~lvl ~message =
  let method_ = "window/logMessage" in
  let params = [ ("type", `Int lvl); ("message", `String message) ] in
  let msg = Base.mk_notification ~method_ ~params in
  send_json !oc msg

let logTrace ~message ~extra =
  let method_ = "$/logTrace" in
  let params =
    match (!trace_value, extra) with
    | Verbose, Some extra ->
      [ ("message", `String message); ("verbose", `String extra) ]
    | _, _ -> [ ("message", `String message) ]
  in
  Base.mk_notification ~method_ ~params |> send_json !oc

let trace hdr ?extra msg =
  let message = Format.asprintf "[%s]: @[%s@]" hdr msg in
  logTrace ~message ~extra

let trace_object hdr obj =
  let message =
    Format.asprintf "[%s]: @[%a@]" hdr Yojson.Safe.(pretty_print ~std:false) obj
  in
  (* Fixme, use the extra parameter *)
  trace hdr message

let () = log := trace_object
