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

let mut = Mutex.create ()
let debug_chan = ref None

let start_log ~client_cb file =
  let abs_file = Filename.concat (Sys.getcwd ()) file in
  try
    let debug_oc = open_out file in
    debug_chan := Some (debug_oc, Format.formatter_of_out_channel debug_oc);
    client_cb (Format.asprintf "server log file %s created" abs_file)
  with _ ->
    client_cb (Format.asprintf "creation of server log file %s failed" abs_file)

let end_log () =
  Option.iter
    (fun (oc, fmt) ->
      Format.pp_print_flush fmt ();
      Stdlib.flush oc;
      close_out oc)
    !debug_chan;
  debug_chan := None

let with_log f = Option.iter (fun (_, fmt) -> f fmt) !debug_chan

let log_error hdr msg =
  with_log (fun fmt ->
      Mutex.lock mut;
      Format.fprintf fmt "[%s]: @[%s@]@\n%!" hdr msg;
      Mutex.unlock mut)

let log_object hdr obj =
  with_log (fun fmt ->
      Format.fprintf fmt "[%s]: @[%a@]@\n%!" hdr
        Yojson.Safe.(pretty_print ~std:false)
        obj)
