(************************************************************************)
(* Coq Language Server Protocol -- Common requests routines             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(* XXX: this doesn't work for Unicode either... *)
(* Common with completion... refactor and make proper *)
let is_id_char x =
  ('a' <= x && x <= 'z')
  || ('A' <= x && x <= 'Z')
  || ('0' <= x && x <= '9')
  || x = '_' || x = '\'' || x = '.'

let rec find_start s c =
  if c <= 0 then 0
  else if not (is_id_char s.[c - 1]) then c
  else find_start s (c - 1)

let id_from_start s start =
  let l = String.length s in
  let rec end_of_id s c =
    if c >= l then c else if is_id_char s.[c] then end_of_id s (c + 1) else c
  in
  let end_ = end_of_id s start in
  (* Correct for last dot *)
  let end_ = if end_ > 1 && s.[end_ - 1] = '.' then end_ - 1 else end_ in
  if start < end_ then (
    let id = String.sub s start (end_ - start) in
    Lsp.Io.trace "find_id" ("found: " ^ id);
    Some id)
  else None

let find_id s c =
  let start = find_start s c in
  Lsp.Io.trace "find_id" ("start: " ^ string_of_int start);
  id_from_start s start

let get_id_at_point ~contents ~point =
  let line, character = point in
  Lsp.Io.trace "get_id_at_point"
    ("l: " ^ string_of_int line ^ " c: " ^ string_of_int character);
  let { Fleche.Contents.lines; _ } = contents in
  if line <= Array.length lines then
    let line = Array.get lines line in
    (* XXX UTF this will fail on unicode chars that differ among UTF-8/16 (cc
       #531) *)
    match Coq.Utf8.index_of_char ~line ~char:character with
    | None -> None
    | Some character -> find_id line character
  else None
