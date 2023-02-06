(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type t =
  { line : int
  ; character : int
  ; offset : int
  }

let pp fmt { line; character; offset } =
  Format.fprintf fmt "{ l: %d, c: %d | o: %d }" line character offset
