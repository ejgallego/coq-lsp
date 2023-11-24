(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Extra : sig
  type t =
    | FailedRequire of
        { prefix : Libnames.qualid option
        ; refs : Libnames.qualid list
        }
end

module Severity : sig
  type t

  val error : t
  val warning : t
  val information : t
  val hint : t

  (** Convert to LSP-like levels *)
  val to_int : t -> int
end

type t =
  { range : Range.t
  ; severity : Severity.t
  ; message : Pp.t
  ; extra : Extra.t list option
  }

val is_error : t -> bool
