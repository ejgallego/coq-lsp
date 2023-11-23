(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2023 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module Extra = struct
  type t =
    | FailedRequire of
        { prefix : Libnames.qualid option
        ; refs : Libnames.qualid list
        }
end

module Severity = struct
  type t = int

  let error = 1
  let warning = 2
  let information = 3
  let hint = 4
  let to_int x = x
end

type t =
  { range : Range.t
  ; severity : Severity.t
  ; message : Pp.t
  ; extra : Extra.t list option
  }

let is_error { severity; _ } = severity = 1
