(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type t =
  { start : Point.t
  ; end_ : Point.t
  }

let pp fmt { start; end_ } =
  Format.fprintf fmt "(@[%a@]--@[%a@])" Point.pp start Point.pp end_

let to_string r = Format.asprintf "%a" pp r
