(************************************************************************)
(* Coq Language Server Protocol -- Common requests routines             *)
(* Copyright 2019 MINES ParisTech -- Dual License LGPL 2.1 / GPL3+      *)
(* Copyright 2019-2024 Inria      -- Dual License LGPL 2.1 / GPL3+      *)
(* Written by: Emilio J. Gallego Arias                                  *)
(************************************************************************)

type t

(* Lookup module as needed *)
val make : Names.DirPath.t -> (t, Loadpath.Error.t) Result.t
val uri : t -> Lang.LUri.File.t
val source : t -> string
val find : t -> string -> (Lang.Range.t option, string) Result.t
