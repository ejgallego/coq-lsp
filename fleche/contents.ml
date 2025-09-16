(************************************************************************)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+     *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1+ / GPL3+     *)
(* Copyright 2024-2025 Emilio J. Gallego Arias -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                    -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)
(* Flèche => document manager: Document Contents                        *)
(************************************************************************)

module R = struct
  (** We want to replace the string by a proper diagnostic we can send to the
      client *)
  type 'a t =
    | Ok of 'a
    | Error of string

  let map ~f = function
    | Ok x -> Ok (f x)
    | Error e -> Error e
end

module Util = struct
  (** Builds a string that contains the right white-space padding between two
      points *)
  let build_whitespace prev cur =
    let l_p, c_p, o_p = Lang.Point.(prev.line, prev.character, prev.offset) in
    let l_c, c_c, o_c = Lang.Point.(cur.line, cur.character, cur.offset) in
    let nl = l_c - l_p in
    let nc, padding = if l_p = l_c then (c_c - c_p, 0) else (c_c, o_c - o_p) in
    String.make padding ' ' ^ String.make nl '\n' ^ String.make nc ' '

  let extract_raw ~raw ~(range : Lang.Range.t) =
    let start = range.start.offset in
    let length = range.end_.offset - start in
    (* We need to be careful here as Doc.t always adds a last empty node on EOF,
       but somehow the offset of this node seems suspicious, it seems like the
       Coq parser increases the offset by one, we need to investigate. *)
    let length =
      if String.length raw < start + length then String.length raw - start
      else length
    in
    String.sub raw start length
end

module Markdown = struct
  let gen l = String.make (String.length l) ' '

  let rec md_map_lines coq l =
    match l with
    | [] -> []
    | l :: ls ->
      (* opening vs closing a markdown block *)
      let code_marker = if coq then [ "```" ] else [ "```coq"; "```rocq" ] in
      let check l c = List.exists (String.equal c) l in
      if check code_marker l then gen l :: md_map_lines (not coq) ls
      else (if coq then l else gen l) :: md_map_lines coq ls

  let process text =
    let lines = String.split_on_char '\n' text in
    let lines = md_map_lines false lines in
    String.concat "\n" lines
end

module LaTeX = struct
  let gen l = String.make (String.length l) ' '

  let rec tex_map_lines coq l =
    match l with
    | [] -> []
    | l :: ls ->
      (* opening vs closing a markdown block *)
      let code_marker = if coq then "\\end{coq}" else "\\begin{coq}" in
      if String.equal code_marker l then gen l :: tex_map_lines (not coq) ls
      else (if coq then l else gen l) :: tex_map_lines coq ls

  let process text =
    let lines = String.split_on_char '\n' text in
    let lines = tex_map_lines false lines in
    String.concat "\n" lines
end

module WaterProof = struct
  open Fleche_waterproof.Json

  let wp_error msg = R.Error (Format.asprintf "Waterproof parsing: %s" msg)

  let code_block block =
    match block with
    | { CAst.v = Assoc dict; _ } -> (
      match find "type" dict with
      | Some { CAst.v = String "code"; _ } -> (
        match find "text" dict with
        | Some { CAst.v = String coq_span; range } -> Some (range, coq_span)
        | _ -> None)
      | _ -> None)
    | _ -> None

  (* Needed to support "text": "\nfoo. bar." in Waterproof files *)
  let new_to_space = function
    | '\n' -> ' '
    | x -> x

  let coq_block_to_span (contents, last_point) (range, coq) =
    let range_text = Util.build_whitespace last_point range.Lang.Range.start in
    let last_point = range.Lang.Range.end_ in
    let coq = String.map new_to_space coq in
    (contents ^ range_text ^ coq, last_point)

  let block_pos (range, _) = Format.asprintf "%a" Lang.Range.pp range
  let waterproof_debug = false

  let from_blocks blocks =
    let start_point = Lang.Point.{ line = 0; character = 0; offset = 0 } in
    let code_blocks = List.filter_map code_block blocks in
    let code_pos = List.map block_pos code_blocks in
    let contents, _ =
      List.fold_left coq_block_to_span ("", start_point) code_blocks
    in
    (if waterproof_debug then
       let code_pos = String.concat "\n" code_pos in
       Io.Log.trace "waterproof" "pos:\n%s\nContents:\n%s" code_pos contents);
    R.Ok contents

  let from_json json =
    match json with
    | CAst.{ v = Assoc dict; _ } -> (
      match find "blocks" dict with
      | None -> wp_error "blocks field not found"
      | Some blocks -> (
        match blocks with
        | { CAst.v = List blocks; _ } -> from_blocks blocks
        | _ -> wp_error "blocks not a list"))
    | _ -> wp_error "top-level object not a dictionary"

  let process raw =
    let lexbuf = Lexing.from_string raw in
    match Fleche_waterproof.(Ljson.prog Tjson.read) lexbuf with
    | None -> R.Ok ""
    | Some json -> from_json json
    | exception _ -> wp_error "parsing failed"
end

let process_contents ~uri ~languageId ~raw =
  let ext = Lang.LUri.File.extension uri in
  match (languageId, ext) with
  | "coq", _ | "rocq", _ -> R.Ok raw
  | "latex", _ -> R.Ok (LaTeX.process raw)
  | "markdown", _ -> R.Ok (Markdown.process raw)
  | _, ".wpn" -> WaterProof.process raw
  | _, _ ->
    let msg =
      Format.asprintf "unknown format: %s for %a" languageId Lang.LUri.File.pp
        uri
    in
    R.Error msg

type t =
  { raw : string  (** That's the original, unprocessed document text *)
  ; text : string
        (** That's the text to be sent to the prover, already processed, encoded
            in UTF-8 *)
  ; last : Lang.Point.t  (** Last point of [text] *)
  ; lines : string Array.t  (** [text] split in lines *)
  }

let get_last_text text =
  let offset = String.length text in
  let lines = CString.split_on_char '\n' text |> Array.of_list in
  let n_lines = Array.length lines in
  let last_line = if n_lines < 1 then "" else Array.get lines (n_lines - 1) in
  let character = Lang.Utf.length_utf16 last_line in
  (Lang.Point.{ line = n_lines - 1; character; offset }, lines)

let make ~uri ~languageId ~raw =
  match process_contents ~uri ~languageId ~raw with
  | R.Error e -> R.Error e
  | R.Ok text ->
    let last, lines = get_last_text text in
    R.Ok { raw; text; last; lines }

let make_raw ~raw =
  let text = raw in
  let last, lines = get_last_text text in
  { raw; text; last; lines }

let extract_raw ~contents:{ raw; _ } ~range = Util.extract_raw ~raw ~range
