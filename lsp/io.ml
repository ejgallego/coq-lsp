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

let read_raw_message ic =
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

let read_raw_message ic =
  try Some (Ok (read_raw_message ic)) with
  (* if the end of input is encountered while some more characters are needed to
     read the current conversion specification, or the lsp server closes *)
  | End_of_file -> None
  (* if the input does not match the format. *)
  | Scanf.Scan_failure msg
  (* if a conversion to a number is not possible. *)
  | Failure msg
  (* if the format string is invalid. *)
  | Invalid_argument msg -> Some (Error msg)

let mut = Mutex.create ()

(* This needs a fix as to log protocol stuff not using the protocol *)
let log = ref (fun _ _ -> ())

let send_json fmt obj =
  Mutex.lock mut;
  if Fleche.Debug.send then !log "send" obj;
  let msg =
    if !Fleche.Config.v.pp_json then
      F.asprintf "%a" J.(pretty_print ~std:true) obj
    else J.to_string obj ^ "\n"
  in
  let size = String.length msg in
  F.fprintf fmt "Content-Length: %d\r\n\r\n%s%!" size msg;
  Mutex.unlock mut

let send_message fmt message = send_json fmt (Base.Message.to_yojson message)

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

module Lvl = struct
  (* 1-5 *)
  type t = Fleche.Io.Level.t =
    | Error
    | Warning
    | Info
    | Log
    | Debug

  let to_int = function
    | Error -> 1
    | Warning -> 2
    | Info -> 3
    | Log -> 4
    | Debug -> 5
end

module MessageParams = struct
  let method_ = "window/logMessage"

  type t =
    { type_ : int [@key "type"]
    ; message : string
    }
  [@@deriving yojson]
end

let mk_logMessage ~type_ ~message =
  let module M = MessageParams in
  let method_ = M.method_ in
  let params =
    M.({ type_; message } |> to_yojson |> Yojson.Safe.Util.to_assoc)
  in
  Base.Notification.make ~method_ ~params ()

let logMessage ~lvl ~message =
  let type_ = Lvl.to_int lvl in
  mk_logMessage ~type_ ~message |> !fn

let logMessageInt ~lvl ~message = mk_logMessage ~type_:lvl ~message |> !fn

module TraceParams = struct
  let method_ = "$/logTrace"

  type t =
    { message : string
    ; verbose : string option [@default None]
    }
  [@@deriving yojson]
end

let mk_logTrace ~message ~extra =
  let module M = TraceParams in
  let method_ = M.method_ in
  let verbose =
    match (!trace_value, extra) with
    | Verbose, Some extra -> Some extra
    | _ -> None
  in
  let params =
    M.({ message; verbose } |> to_yojson |> Yojson.Safe.Util.to_assoc)
  in
  Base.Notification.make ~method_ ~params ()

let logTrace ~message ~extra = mk_logTrace ~message ~extra |> !fn

(* Disabled for now, see comment above *)
(* let () = log := trace_object *)

(** Misc helpers *)
let read_message ic =
  match read_raw_message ic with
  | None -> None (* EOF *)
  | Some (Ok com) ->
    if Fleche.Debug.read then !log "read" com;
    Some (Base.Message.of_yojson com)
  | Some (Error err) -> Some (Error err)
