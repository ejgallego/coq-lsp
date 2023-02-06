(************************************************************************)
(* Flèche => document manager: Document Contents                        *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
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

module WaterProof = struct
  let process _raw = R.Error "waterproof parsing not yet supported"
end

let process_contents ~uri ~raw =
  let ext = Filename.extension uri in
  match ext with
  | ".v" -> R.Ok raw
  | ".mv" -> R.Ok (Markdown.process raw)
  | ".wpn" -> WaterProof.process raw
  | _ -> R.Error "unknown file format"

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
  let character = Utf8.length last_line in
  (Lang.Point.{ line = n_lines - 1; character; offset }, lines)

let make ~uri ~raw =
  match process_contents ~uri ~raw with
  | R.Error e -> R.Error e
  | R.Ok text ->
    let last, lines = get_last_text text in
    R.Ok { raw; text; last; lines }
