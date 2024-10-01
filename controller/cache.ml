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

module L = Fleche.Io.Log

(* Cache stuff *)
let memo_cache_file = ".coq-lsp.cache"

let memo_save_to_disk () =
  try
    Fleche.Memo.save_to_disk ~file:memo_cache_file;
    L.trace "memo" "cache saved to disk"
  with exn ->
    L.trace "memo" "%s" (Printexc.to_string exn);
    Sys.remove memo_cache_file;
    ()

(* We disable it for now, see todo.org for more information *)
let save_to_disk () = if true then memo_save_to_disk ()

let memo_read_from_disk () =
  try
    if Sys.file_exists memo_cache_file then (
      L.trace "memo" "trying to load cache file";
      Fleche.Memo.load_from_disk ~file:memo_cache_file;
      L.trace "memo" "cache file loaded")
    else L.trace "memo" "cache file not present"
  with exn ->
    L.trace "memo" "loading cache failed: %s" (Printexc.to_string exn);
    Sys.remove memo_cache_file;
    ()

let read_from_disk () = if true then memo_read_from_disk ()
