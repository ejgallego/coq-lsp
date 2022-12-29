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

module TraceValue = struct
  type t =
    | Off
    | Messages
    | Verbose

  let parse = function
    | "messages" -> Messages
    | "verbose" -> Verbose
    | "off" -> Off
    | _ -> raise (Invalid_argument "TraceValue.parse")

  let to_string = function
    | Off -> "off"
    | Messages -> "messages"
    | Verbose -> "verbose"
end

let trace_value = ref TraceValue.Off
let set_trace_value value = trace_value := value

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

let send_json fmt obj =
  Mutex.lock mut;
  let msg = F.asprintf "%a" J.(pretty_print ~std:true) obj in
  let size = String.length msg in
  F.fprintf fmt "Content-Length: %d\r\n\r\n%s%!" size msg;
  Mutex.unlock mut

let logMessage fmt ~lvl ~message =
  let method_ = "window/logMessage" in
  let params = [ ("type", `Int lvl); ("message", `String message) ] in
  let msg = Base.mk_notification ~method_ ~params in
  send_json fmt msg

let logTrace fmt ~verbose ~message =
  let method_ = "$/logTrace" in
  if !trace_value = TraceValue.parse verbose then
    if !trace_value = TraceValue.Messages then
      let params = [ ("message", `String message) ] in
      let msg = Base.mk_notification ~method_ ~params in
      send_json fmt msg
    else if !trace_value = TraceValue.Verbose then
      let params =
        [ ("message", `String message); ("verbose", `String verbose) ]
      in
      let msg = Base.mk_notification ~method_ ~params in
      send_json fmt msg

let log_info hdr msg =
  logTrace F.std_formatter ~verbose:"verbose"
    ~message:(Format.asprintf "[%s]: @[%s@]@\n%!" hdr msg)

let log_error hdr msg =
  logTrace F.std_formatter ~verbose:"messages"
    ~message:(Format.asprintf "[%s]: @[%s@]@\n%!" hdr msg)

let log_object hdr obj =
  logTrace F.std_formatter ~verbose:"verbose"
    ~message:
      (Format.asprintf "[%s]: @[%a@]@\n%!" hdr
         Yojson.Safe.(pretty_print ~std:false)
         obj)
