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
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias & Bhakti Shah                    *)
(************************************************************************)

module DefMap = CString.Map

module Error = struct
  type t =
    | Ill_formed of string
    | Outdated

  let to_string = function
    | Ill_formed s -> "Ill-formed file: " ^ s
    | Outdated -> "Outdated .glob file"
end

module Info = struct
  type t =
    { kind : string
    ; offset : int * int
    }
end

(* This is taken from coqdoc/glob_file.ml , we should share this code, but no
   cycles ATM *)
module Coq = struct
  module Entry_type = struct
    type t =
      | Library
      | Module
      | Definition
      | Inductive
      | Constructor
      | Lemma
      | Record
      | Projection
      | Instance
      | Class
      | Method
      | Variable
      | Axiom
      | TacticDefinition
      | Abbreviation
      | Notation
      | Section
      | Binder

    let of_string = function
      | "def"
      | "coe"
      | "subclass"
      | "canonstruc"
      | "fix"
      | "cofix"
      | "ex"
      | "scheme" -> Definition
      | "prf" | "thm" -> Lemma
      | "ind" | "variant" | "coind" -> Inductive
      | "constr" -> Constructor
      | "indrec" | "rec" | "corec" -> Record
      | "proj" -> Projection
      | "class" -> Class
      | "meth" -> Method
      | "inst" -> Instance
      | "var" -> Variable
      | "defax" | "prfax" | "ax" -> Axiom
      | "abbrev" | "syndef" -> Abbreviation
      | "not" -> Notation
      | "lib" -> Library
      | "mod" | "modtype" -> Module
      | "tac" -> TacticDefinition
      | "sec" -> Section
      | "binder" -> Binder
      | s -> invalid_arg ("type_of_string:" ^ s)
  end

  let read_dp ic =
    let line = input_line ic in
    let n = String.length line in
    match line.[0] with
    | 'F' ->
      let lib_name = String.sub line 1 (n - 1) in
      Ok lib_name
    | _ -> Error (Error.Ill_formed "lib name not found in header")

  let correct_file vfile ic =
    let s = input_line ic in
    if String.length s < 7 || String.sub s 0 7 <> "DIGEST " then
      Error (Error.Ill_formed "DIGEST ill-formed")
    else
      let s = String.sub s 7 (String.length s - 7) in
      match (vfile, s) with
      | None, "NO" -> read_dp ic
      | Some _, "NO" -> Error (Ill_formed "coming from .v file but no digest")
      | None, _ -> Error (Ill_formed "digest but .v source file not available")
      | Some vfile, s ->
        if s = Digest.to_hex (Digest.file vfile) then
          (* XXX Read F line *)
          read_dp ic
        else Error Outdated

  let parse_ref line =
    try
      (* Disable for now *)
      if false then
        let add_ref _ _ _ _ _ = () in
        Scanf.sscanf line "R%d:%d %s %s %s %s" (fun loc1 loc2 lib_dp sp id ty ->
            for loc = loc1 to loc2 do
              add_ref loc lib_dp sp id (Entry_type.of_string ty);
              (* Also add an entry for each module mentioned in [lib_dp], * to
                 use in interpolation. *)
              ignore
                (List.fold_right
                   (fun thisPiece priorPieces ->
                     let newPieces =
                       match priorPieces with
                       | "" -> thisPiece
                       | _ -> thisPiece ^ "." ^ priorPieces
                     in
                     add_ref loc "" "" newPieces Entry_type.Library;
                     newPieces)
                   (Str.split (Str.regexp_string ".") lib_dp)
                   "")
            done)
    with _ -> ()

  let parse_def line : _ Result.t =
    try
      Scanf.sscanf line "%s %d:%d %s %s"
        (fun kind loc1 loc2 section_path name ->
          Ok (name, section_path, kind, (loc1, loc2)))
    with Scanf.Scan_failure err -> Error err

  let process_line dp map line =
    match line.[0] with
    | 'R' ->
      let _reference = parse_ref line in
      map
    | _ -> (
      match parse_def line with
      | Error _ -> map
      | Ok (name, section_path, kind, offset) ->
        let section_path =
          if String.equal "<>" section_path then "" else section_path ^ "."
        in
        let name = dp ^ "." ^ section_path ^ name in
        let info = { Info.kind; offset } in
        DefMap.add name info map)

  let read_glob vfile inc =
    match correct_file vfile inc with
    | Error e -> Error (Error.to_string e)
    | Ok dp -> (
      let map = ref DefMap.empty in
      try
        while true do
          let line = input_line inc in
          let n = String.length line in
          if n > 0 then map := process_line dp !map line
        done;
        assert false
      with End_of_file -> Ok !map)
end

(* Glob file that was read and parsed successfully *)
type t = Info.t DefMap.t

let open_file file =
  if Sys.file_exists file then
    let vfile = Filename.remove_extension file ^ ".v" in
    Compat.Ocaml_414.In_channel.with_open_text file (Coq.read_glob (Some vfile))
  else Error (Format.asprintf "Cannot open file: %s" file)

let get_info map name = DefMap.find_opt name map
