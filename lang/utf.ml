(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

(** This module provides facilities for translating language-based locations to
    protocol-based locations.

    After a long discussion (thanks Léo !), we have decided that the best is to
    have `Lang.Point` to store columns offset in the values that are native to
    the protocol under consideration, set by the upper layers.

    This scheme kind of follows what we have done since the start with coq-lsp. *)
module Encoding = struct
  (* Used for char offsets *)
  type t =
    | Utf8
    | Utf16
    | Utf32
end
