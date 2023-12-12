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
(* Copyright 2019 MINES ParisTech -- LGPL 2.1+                          *)
(* Copyright 2019-2023 Inria -- LGPL 2.1+                               *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

open Lsp.Core

let mk_completion ~label ?insertText ?labelDetails ?textEdit ?commitCharacters
    () =
  CompletionData.(
    to_yojson { label; insertText; labelDetails; textEdit; commitCharacters })

let grab_definitions ~doc ~f =
  let asts = Fleche.Doc.asts doc in
  let df { Fleche.Doc.Node.Ast.ast_info; _ } = ast_info in
  List.filter_map df asts |> List.concat |> List.filter_map f

let build_doc_idents ~doc : Yojson.Safe.t list =
  let f { Lang.Ast.Info.name; _ } =
    match name.v with
    | None -> None
    | Some id -> Some (mk_completion ~label:id ())
  in
  grab_definitions ~doc ~f

let mk_completion_list ~incomplete ~items : Yojson.Safe.t =
  `Assoc [ ("isIncomplete", `Bool incomplete); ("items", `List items) ]

let mk_edit (line, character) newText =
  let open Lang in
  let insert =
    Range.
      { start = { Point.line; character = character - 1; offset = -1 }
      ; end_ = { Point.line; character; offset = -1 }
      }
  in
  let replace = insert in
  TextEditReplace.{ insert; replace; newText }

let unicode_commit_chars =
  [ " "; "("; ")"; ","; "."; "-"; "'" ]
  @ [ "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9" ]

let mk_unicode_completion_item point (label, newText) =
  let labelDetails = LabelDetails.{ detail = " ← " ^ newText } in
  let textEdit = mk_edit point newText in
  let commitCharacters = unicode_commit_chars in
  mk_completion ~label ~labelDetails ~textEdit ~commitCharacters ()

let unicode_list point : Yojson.Safe.t list =
  let ulist =
    match !Fleche.Config.v.unicode_completion with
    | Off -> []
    | Internal_small -> Unicode_bindings.small
    | Normal -> Unicode_bindings.normal
    | Extended -> Unicode_bindings.extended
  in
  (* Coq's CList.map is tail-recursive *)
  CList.map (mk_unicode_completion_item point) ulist

let validate_line ~(doc : Fleche.Doc.t) ~line =
  if Array.length doc.contents.lines > line then
    Some (Array.get doc.contents.lines line)
  else None

(* This returns a byte-based char offset for the line *)
let validate_position ~doc ~point =
  let line, char = point in
  Option.map
    (fun line ->
      let char = Coq.Utf8.get_byte_offset_from_utf16_pos line char in
      String.get line char)
    (validate_line ~doc ~line)

let get_char_at_point ~(doc : Fleche.Doc.t) ~point =
  let line, char = point in
  if char >= 1 then
    let point = (line, char - 1) in
    validate_position ~doc ~point
  else (* Can't get previous char *)
    None

(* point is a utf char! *)
let completion ~doc ~point =
  (* Instead of get_char_at_point we should have a CompletionContext.t, to be
     addressed in further completion PRs *)
  (match get_char_at_point ~doc ~point with
  | None ->
    let incomplete = true in
    let items = [] in
    mk_completion_list ~incomplete ~items
  | Some c ->
    let incomplete, items =
      if c = '\\' then (false, unicode_list point)
      else (true, build_doc_idents ~doc)
    in
    let res = mk_completion_list ~incomplete ~items in
    res)
  |> Result.ok
