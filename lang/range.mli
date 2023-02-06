(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type t =
  { start : Point.t
  ; end_ : Point.t [@key "end"]
  }

val pp : Format.formatter -> t -> unit
val to_string : t -> string
