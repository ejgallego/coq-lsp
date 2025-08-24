(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type t = string

let of_string = Fun.id
let to_string = Fun.id
let is_file_path _ = true

module File = struct
  type uri = t

  type t =
    { uri : uri
    ; file : string
    }

  let of_uri uri =
    if String.length uri > 0 then
      if Char.equal uri.[0] '/' then Result.Ok { uri; file = uri }
      else Result.Ok { uri; file = String.sub uri 8 (String.length uri - 8) }
    else Result.Ok { uri = ""; file = "" }

  let to_string_uri { uri; _ } = uri
  let to_string_file { file; _ } = file
  let extension { file; _ } = Filename.extension file
  let hash = Hashtbl.hash
  let compare = Stdlib.compare
  let equal = Stdlib.( = )
  let pp fmt uri = Format.fprintf fmt "%s" uri.uri
end
