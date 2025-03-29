(************************************************************************)
(* Rocq Language Server Protocol                                        *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2024-2025 EJGA       -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module F = Format
module J = Yojson.Safe

(** {1 JSON-RPC input/output} *)

(* This needs a fix as to log protocol stuff not using the protocol *)
let log_protocol = ref (fun _ _ -> ())
let set_log_fn fn = log_protocol := fn

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

let read_message ic =
  match read_raw_message ic with
  | None -> None (* EOF *)
  | Some (Ok com) ->
    !log_protocol "read" com;
    Some (Base.Message.of_yojson com)
  | Some (Error err) -> Some (Error err)

let mut = Mutex.create ()

let send_json fmt obj =
  Mutex.lock mut;
  !log_protocol "send" obj;
  let msg =
    if !Fleche.Config.v.pp_json then
      F.asprintf "%a" J.(pretty_print ~std:true) obj
    else J.to_string obj ^ "\n"
  in
  let size = String.length msg in
  F.fprintf fmt "Content-Length: %d\r\n\r\n%s%!" size msg;
  Mutex.unlock mut

let send_message fmt message = send_json fmt (Base.Message.to_yojson message)
