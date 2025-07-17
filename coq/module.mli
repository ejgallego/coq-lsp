(*************************************************************************)
(* Copyright 2015-2019 MINES ParisTech -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2019-2024 Inria           -- Dual License LGPL 2.1+ / GPL3+ *)
(* Copyright 2024-2025 Emilio J. Gallego Arias  -- LGPL 2.1+ / GPL3+     *)
(* Copyright 2025      CNRS                     -- LGPL 2.1+ / GPL3+     *)
(* Written by: Emilio J. Gallego Arias & coq-lsp contributors            *)
(*************************************************************************)
(* Rocq Language Server Protocol: Rocq module API                        *)
(*************************************************************************)

type t

(* Lookup module as needed *)
val make : Names.DirPath.t -> (t, Exninfo.iexn) Result.t
val uri : t -> Lang.LUri.File.t
val source : t -> string
val find : t -> string -> (Lang.Range.t option, string) Result.t
