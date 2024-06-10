(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type t = Uri.t

let of_string = Uri.of_string
let is_file_path _ = true

module File = struct
  type uri = t

  type t =
    { uri : uri
    ; file : string
    }

  let of_uri uri = Result.Ok { uri; file = Uri.pct_decode (Uri.path uri) }
  let to_string_uri { uri; _ } = Uri.to_string uri
  let to_string_file { file; _ } = file
  let extension { file; _ } = Filename.extension file
  let hash = Hashtbl.hash
  let compare = Stdlib.compare
  let equal = Stdlib.( = )
  let pp fmt uri = Format.fprintf fmt "%a" Uri.pp uri.uri
end
