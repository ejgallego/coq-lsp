(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type 'l t =
  { range : 'l
  ; newText : string
  }

let map ~f { range; newText } = { range = f range; newText }
