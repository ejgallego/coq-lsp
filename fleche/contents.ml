(************************************************************************)
(* Flèche => document manager: Document Contents                        *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Markdown = struct
  let gen l = String.make (String.length l) ' '

  let rec md_map_lines coq l =
    match l with
    | [] -> []
    | l :: ls ->
      (* opening vs closing a markdown block *)
      let code_marker = if coq then "```" else "```coq" in
      if String.equal code_marker l then gen l :: md_map_lines (not coq) ls
      else (if coq then l else gen l) :: md_map_lines coq ls

  let process text =
    let lines = String.split_on_char '\n' text in
    let lines = md_map_lines false lines in
    String.concat "\n" lines
end

let process_contents ~uri ~contents =
  let ext = Filename.extension uri in
  let is_markdown = String.equal ext ".mv" in
  if is_markdown then Markdown.process contents else contents

type t =
  { raw : string  (** That's the original, unprocessed document text *)
  ; text : string
        (** That's the text to be sent to the prover, already processed, encoded
            in UTF-8 *)
  ; last : Types.Point.t  (** Last point of [text] *)
  ; lines : string Array.t  (** [text] split in lines *)
  }

let get_last_text text =
  let offset = String.length text in
  let lines = CString.split_on_char '\n' text |> Array.of_list in
  let n_lines = Array.length lines in
  let last_line = if n_lines < 1 then "" else Array.get lines (n_lines - 1) in
  let character = Utf8.length last_line in
  (Types.Point.{ line = n_lines - 1; character; offset }, lines)

let make ~uri ~raw =
  let text = process_contents ~uri ~contents:raw in
  let last, lines = get_last_text text in
  { raw; text; last; lines }
