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

open Base
open Ppx_hash_lib.Std.Hash.Builtin
open Ppx_compare_lib.Builtin

type t = int [@@deriving hash, compare]

let make () = 0
let bump i = i + 1

let qualid_to_dirpath qid =
  let hd, tl = Libnames.repr_qualid qid in
  Libnames.add_dirpath_suffix hd tl

module Require_result = struct
  type t =
    | Ready of
        (Names.DirPath.t * CUnix.physical_path, Loadpath.Error.t) Result.t list
    | Wait of CUnix.physical_path list
end

let check_file_ready ?root (m, _imports) =
  match Loadpath.locate_qualified_library ?root m with
  | Ok (dirpath, file) ->
    let () =
      Stdlib.Format.eprintf "found file: %s for library %s@\n%!" file
        (Names.DirPath.to_string dirpath)
    in
    let ready = true in
    (* Hook for the document manager *)
    if ready then Ok (Ok (dirpath, file)) else Error file
  | Error e -> Ok (Error e)

let requires_are_ready ~files:_ { Ast.Require.from; export = _; mods; _ } =
  let root = Option.map ~f:qualid_to_dirpath from in
  match List.map ~f:(check_file_ready ?root) mods |> Result.combine_errors with
  | Ok r -> Require_result.Ready r
  | Error f -> Wait f
