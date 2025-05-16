(************************************************************************)
(* Flèche => document manager: Language Support                         *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

module FailedRequire = struct
  type t =
    { prefix : Libnames.qualid option
    ; refs : Libnames.qualid list
    }
end

module Data = struct
  type t =
    { sentenceRange : Range.t option [@default None]
    ; failedRequire : FailedRequire.t list option [@default None]
    ; quickFix : Range.t Qf.t list option [@default None]
    }
end

module Severity = struct
  type t = int

  let error = 1
  let warning = 2
  let information = 3
  let hint = 4

  let of_string s = match s with
    | "error" -> Ok 1
    | "warning" -> Ok 2
    | "information" -> Ok 3
    | "hint" -> Ok 4
    | other -> Error ("The string " ^ other ^ " does not correspond to any existing severity.")

  let to_string s = match s with
    | 1 -> "error"
    | 2 -> "warning"
    | 3 -> "information"
    | 4 -> "hint"
    | _ -> "unknown"
end

type t =
  { range : Range.t
  ; severity : Severity.t
  ; message : Pp.t
  ; data : Data.t option [@default None]
  }

let is_error { severity; _ } = severity = 1
