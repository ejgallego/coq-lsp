(************************************************************************)
(* Flèche => document manager: Document                                 *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2024-2025 Emilio J. Gallego Arias -- LGPL 2.1 / GPL3+      *)
(* Copyright 2025      CNRS                    -- LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors           *)
(************************************************************************)

(** Abstraction module over Rocq versions and their characteristics *)

(* Not safe until we merge PR upstream #19177 *)
let sane_coq_base_version = false

let is_lsp_branch =
  CString.string_contains ~where:Coq_config.version ~what:"+lsp"

let safe_coq = sane_coq_base_version || is_lsp_branch
let safe_for_memprof = safe_coq

let quirks_message =
  Format.asprintf "Rocq safe for memprof-limits: %b" safe_for_memprof
