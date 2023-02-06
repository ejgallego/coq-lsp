(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(** ATTENTION: [character] is a Unicode caracter position, thus from Coq that
    usually requires conversion, as it will report the column offset in bytes.
    But [offset] is in bytes for now, as our downstream clients prefer this
    format. *)
type t =
  { line : int
  ; character : int
  ; offset : int
  }

val pp : Format.formatter -> t -> unit
