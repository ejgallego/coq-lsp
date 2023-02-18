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
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module LIO = Lsp.Io

(* Cache stuff *)
let memo_cache_file = ".coq-lsp.cache"

let memo_save_to_disk () =
  try
    (* Fleche.Memo.save_to_disk ~file:memo_cache_file; *)
    LIO.trace "memo" "cache saved to disk"
  with exn ->
    LIO.trace "memo" (Printexc.to_string exn);
    Sys.remove memo_cache_file;
    ()

(* We disable it for now, see todo.org for more information *)
let save_to_disk () = if false then memo_save_to_disk ()

let memo_read_from_disk () =
  try
    if Sys.file_exists memo_cache_file then (
      LIO.trace "memo" "trying to load cache file";
      (* Fleche.Memo.load_from_disk ~file:memo_cache_file; *)
      LIO.trace "memo" "cache file loaded")
    else LIO.trace "memo" "cache file not present"
  with exn ->
    LIO.trace "memo" ("loading cache failed: " ^ Printexc.to_string exn);
    Sys.remove memo_cache_file;
    ()

let read_from_disk () = if false then memo_read_from_disk ()
