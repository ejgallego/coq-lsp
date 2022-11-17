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
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)
(* Status: Experimental                                                 *)
(************************************************************************)

module F = Format
module J = Yojson.Safe

let mut = Mutex.create ()
let debug_fmt = ref F.err_formatter

let log_error hdr msg =
  Mutex.lock mut;
  F.fprintf !debug_fmt "[%s]: @[%s@]@\n%!" hdr msg;
  Mutex.unlock mut

let log_object hdr obj =
  F.fprintf !debug_fmt "[%s]: @[%a@]@\n%!" hdr J.(pretty_print ~std:false) obj

let flush_log () = F.pp_print_flush !debug_fmt ()

exception ReadError of string

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

let send_json fmt obj =
  Mutex.lock mut;
  if Fleche.Debug.send then log_object "send" obj;
  let msg = F.asprintf "%a" J.(pretty_print ~std:true) obj in
  let size = String.length msg in
  F.fprintf fmt "Content-Length: %d\r\n\r\n%s%!" size msg;
  Mutex.unlock mut
