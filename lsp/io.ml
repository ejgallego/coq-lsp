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

let fn = ref (fun _ -> ())
let set_log_fn f = fn := f

let read_raw_request ic =
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

let read_raw_request ic =
  try Some (read_raw_request ic) with
  (* if the end of input is encountered while some more characters are needed to
     read the current conversion specification, or the lsp server closes *)
  | End_of_file -> None
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
  let msg = J.to_string obj in
  let size = String.length msg in
  F.fprintf fmt "Content-Length: %d\r\n\r\n%s\n%!" (size+1) msg;
  Mutex.unlock mut

(** Logging *)

module TraceValue = struct
  type t =
    | Off
    | Messages
    | Verbose

  let of_string = function
    | "messages" -> Ok Messages
    | "verbose" -> Ok Verbose
    | "off" -> Ok Off
    | v -> Error ("TraceValue.parse: " ^ v)

  let to_string = function
    | Off -> "off"
    | Messages -> "messages"
    | Verbose -> "verbose"
end

let trace_value = ref TraceValue.Off
let set_trace_value value = trace_value := value

let logMessage ~lvl ~message =
  let method_ = "window/logMessage" in
  let params = `Assoc [ ("type", `Int lvl); ("message", `String message) ] in
  let msg = Base.mk_notification ~method_ ~params in
  !fn msg

let logTrace ~message ~extra =
  let method_ = "$/logTrace" in
  let params =
    match (!trace_value, extra) with
    | Verbose, Some extra ->
      `Assoc [ ("message", `String message); ("verbose", `String extra) ]
    | _, _ -> `Assoc [ ("message", `String message) ]
  in
  Base.mk_notification ~method_ ~params |> !fn

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

(** Misc helpers *)
let rec read_request ic =
  match read_raw_request ic with
  | None -> None (* EOF *)
  | Some com -> (
    if Fleche.Debug.read then trace_object "read" com;
    match Base.Message.from_yojson com with
    | Ok msg -> Some msg
    | Error msg ->
      trace "read_request" ("error: " ^ msg);
      read_request ic)
